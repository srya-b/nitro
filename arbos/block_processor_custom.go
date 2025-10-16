package arbos

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	"math/big"

	"github.com/ethereum/go-ethereum/arbitrum_types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/trie"

	"github.com/offchainlabs/nitro/arbos/arbosState"
	"github.com/offchainlabs/nitro/arbos/arbostypes"
	"github.com/offchainlabs/nitro/arbos/l2pricing"
	"github.com/offchainlabs/nitro/arbos/util"
	"github.com/offchainlabs/nitro/util/arbmath"
)

func ProduceBlockCustom(
	message *arbostypes.L1IncomingMessage,
	delayedMessagesRead uint64,
	lastBlockHeader *types.Header,
	statedb *state.StateDB,
	chainContext core.ChainContext,
	isMsgForPrefetch bool,
	runCtx *core.MessageRunContext,
) (*types.Block, types.Receipts, error) {
	chainConfig := chainContext.Config()
	txes, err := ParseL2Transactions(message, chainConfig.ChainID)
	if err != nil {
		log.Warn("error parsing incoming message", "err", err)
		txes = types.Transactions{}
	}

	hooks := NoopSequencingHooks(txes)
	return ProduceBlockAdvancedCustom(
		message.Header, delayedMessagesRead, lastBlockHeader, statedb, chainContext, hooks, isMsgForPrefetch, runCtx,
	)
}

// A bit more flexible than ProduceBlock for use in the sequencer.
func ProduceBlockAdvancedCustom(
	l1Header *arbostypes.L1IncomingMessageHeader,
	delayedMessagesRead uint64,
	lastBlockHeader *types.Header,
	statedb *state.StateDB,
	chainContext core.ChainContext,
	sequencingHooks *SequencingHooks,
	isMsgForPrefetch bool,
	runCtx *core.MessageRunContext,
) (*types.Block, types.Receipts, error) {

	arbState, err := arbosState.OpenSystemArbosState(statedb, nil, true)
	if err != nil {
		return nil, nil, err
	}

	if statedb.GetUnexpectedBalanceDelta().BitLen() != 0 {
		return nil, nil, errors.New("ProduceBlock called with dirty StateDB (non-zero unexpected balance delta)")
	}

	poster := l1Header.Poster

	l1Info := &L1Info{
		poster:        poster,
		l1BlockNumber: l1Header.BlockNumber,
		l1Timestamp:   l1Header.Timestamp,
	}

	chainConfig := chainContext.Config()

	header := createNewHeader(lastBlockHeader, l1Info, arbState, chainConfig)
	// Note: blockGasLeft will diverge from the actual gas left during execution in the event of invalid txs,
	// but it's only used as block-local representation limiting the amount of work done in a block.
	blockGasLeft, _ := arbState.L2PricingState().PerBlockGasLimit()
	l1BlockNum := l1Info.l1BlockNumber

	// Prepend a tx before all others to touch up the state (update the L1 block num, pricing pools, etc)
	startTx := InternalTxStartBlock(chainConfig.ChainID, l1Header.L1BaseFee, l1BlockNum, header, lastBlockHeader)

	complete := types.Transactions{}
	receipts := types.Receipts{}
	basefee := header.BaseFee
	time := header.Time
	expectedBalanceDelta := new(big.Int)
	redeems := types.Transactions{}
	userTxsProcessed := 0

	// We'll check that the block can fit each message, so this pool is set to not run out
	gethGas := core.GasPool(l2pricing.GethBlockGasLimit)

	firstTx := types.NewTx(startTx)

	for {
		// repeatedly process the next tx, doing redeems created along the way in FIFO order
		log.Info("New Transaction")

		var tx *types.Transaction
		var options *arbitrum_types.ConditionalOptions
		hooks := NoopSequencingHooks(nil)
		isUserTx := false
		if firstTx != nil {
			tx = firstTx
			firstTx = nil
		} else if len(redeems) > 0 {
			tx = redeems[0]
			redeems = redeems[1:]

			retry, ok := (tx.GetInner()).(*types.ArbitrumRetryTx)
			if !ok {
				return nil, nil, errors.New("retryable tx is somehow not a retryable")
			}
			retryable, _ := arbState.RetryableState().OpenRetryable(retry.TicketId, time)
			if retryable == nil {
				// retryable was already deleted
				continue
			}
		} else {
			tx, err = sequencingHooks.NextTxToSequence()
			if err != nil {
				return nil, nil, fmt.Errorf("error fetching next transaction to sequence, userTxsProcessed: %d, hookTxErrors: %d, err: %w", userTxsProcessed, len(sequencingHooks.TxErrors), err)
			}
			if tx == nil {
				break
			}
			if tx.Type() != types.ArbitrumInternalTxType {
				hooks = sequencingHooks // the sequencer has the ability to drop this tx
				isUserTx = true
				if len(hooks.ConditionalOptionsForTx) > 0 {
					options = hooks.ConditionalOptionsForTx[0]
					hooks.ConditionalOptionsForTx = hooks.ConditionalOptionsForTx[1:]
				}
			}
		}

		startRefund := statedb.GetRefund()
		if startRefund != 0 {
			return nil, nil, fmt.Errorf("at beginning of tx statedb has non-zero refund %v", startRefund)
		}

		var sender common.Address
		var dataGas uint64 = 0
		preTxHeaderGasUsed := header.GasUsed
		signer := types.MakeSigner(chainConfig, header.Number, header.Time, arbState.ArbOSVersion())
		receipt, result, err := (func() (*types.Receipt, *core.ExecutionResult, error) {
			// If we've done too much work in this block, discard the tx as early as possible
			if blockGasLeft < params.TxGas && isUserTx {
				return nil, nil, core.ErrGasLimitReached
			}

			sender, err = signer.Sender(tx)
			if err != nil {
				return nil, nil, err
			}

			// Writes to statedb object should be avoided to prevent invalid state from permeating as statedb snapshot is not taken
			if err = hooks.PreTxFilter(chainConfig, header, statedb, arbState, tx, options, sender, l1Info); err != nil {
				return nil, nil, err
			}

			// Additional pre-transaction validity check
			// Writes to statedb object should be avoided to prevent invalid state from permeating as statedb snapshot is not taken
			if err = extraPreTxFilter(chainConfig, header, statedb, arbState, tx, options, sender, l1Info); err != nil {
				return nil, nil, err
			}

			if basefee.Sign() > 0 {
				dataGas = math.MaxUint64
				brotliCompressionLevel, err := arbState.BrotliCompressionLevel()
				if err != nil {
					return nil, nil, fmt.Errorf("failed to get brotli compression level: %w", err)
				}
				posterCost, _ := arbState.L1PricingState().GetPosterInfo(tx, poster, brotliCompressionLevel)
				posterCostInL2Gas := arbmath.BigDiv(posterCost, basefee)

				if posterCostInL2Gas.IsUint64() {
					dataGas = posterCostInL2Gas.Uint64()
				} else {
					log.Error("Could not get poster cost in L2 terms", "posterCost", posterCost, "basefee", basefee)
				}
			}

			if dataGas > tx.Gas() {
				// this txn is going to be rejected later
				dataGas = tx.Gas()
			}

			computeGas := tx.Gas() - dataGas
			if computeGas < params.TxGas {
				if hooks.DiscardInvalidTxsEarly {
					return nil, nil, core.ErrIntrinsicGas
				}
				// ensure at least TxGas is left in the pool before trying a state transition
				computeGas = params.TxGas
			}

			if computeGas > blockGasLeft && isUserTx && userTxsProcessed > 0 {
				return nil, nil, core.ErrGasLimitReached
			}

			snap := statedb.Snapshot()
			statedb.SetTxContext(tx.Hash(), len(receipts)) // the number of successful state transitions

			gasPool := gethGas
			blockContext := core.NewEVMBlockContext(header, chainContext, &header.Coinbase)
			evm := vm.NewEVM(blockContext, statedb, chainConfig, vm.Config{})
			if statedb.HasLogger() {
				log.Info("<><><><><> Tx boundary start <><><><>")
			}
			receipt, result, err := core.ApplyTransactionWithResultFilter(
				evm,
				&gasPool,
				statedb,
				header,
				tx,
				&header.GasUsed,
				runCtx,
				func(result *core.ExecutionResult) error {
					return hooks.PostTxFilter(header, statedb, arbState, tx, sender, dataGas, result)
				},
			)
			if statedb.HasLogger() {
				log.Info("<><><><> tx boundary stop <><><><>")
			}
			log.Info("Done applying transaction")

			if err != nil {
				// Ignore this transaction if it's invalid under the state transition function
				statedb.RevertToSnapshot(snap)
				statedb.ClearTxFilter()
				return nil, nil, err
			}

			// Additional post-transaction validity check
			if err = extraPostTxFilter(chainConfig, header, statedb, arbState, tx, options, sender, l1Info, result); err != nil {
				statedb.RevertToSnapshot(snap)
				statedb.ClearTxFilter()
				return nil, nil, err
			}

			return receipt, result, nil
		})()

		// append the err, even if it is nil
		hooks.TxErrors = append(hooks.TxErrors, err)

		if err != nil {
			logLevel := log.Debug
			if chainConfig.DebugMode() {
				logLevel = log.Warn
			}
			if !isMsgForPrefetch {
				logLevel("error applying transaction", "tx", printTxAsJson{tx}, "err", err)
			}
			if !hooks.DiscardInvalidTxsEarly {
				// we'll still deduct a TxGas's worth from the block-local rate limiter even if the tx was invalid
				blockGasLeft = arbmath.SaturatingUSub(blockGasLeft, params.TxGas)
				if isUserTx {
					userTxsProcessed++
				}
			}
			continue
		}

		if tx.Type() == types.ArbitrumInternalTxType {
			// ArbOS might have upgraded to a new version, so we need to refresh our state
			arbState, err = arbosState.OpenSystemArbosState(statedb, nil, true)
			if err != nil {
				return nil, nil, err
			}
			// Update the ArbOS version in the header (if it changed)
			extraInfo := types.DeserializeHeaderExtraInformation(header)
			extraInfo.ArbOSFormatVersion = arbState.ArbOSVersion()
			extraInfo.UpdateHeaderWithInfo(header)
		}

		if tx.Type() == types.ArbitrumInternalTxType && result.Err != nil {
			return nil, nil, fmt.Errorf("failed to apply internal transaction: %w", result.Err)
		}

		if preTxHeaderGasUsed > header.GasUsed {
			return nil, nil, fmt.Errorf("ApplyTransaction() used -%v gas", preTxHeaderGasUsed-header.GasUsed)
		}
		txGasUsed := header.GasUsed - preTxHeaderGasUsed

		arbosVer := types.DeserializeHeaderExtraInformation(header).ArbOSFormatVersion
		if arbosVer >= params.ArbosVersion_FixRedeemGas {
			// subtract gas burned for future use
			for _, scheduledTx := range result.ScheduledTxes {
				switch inner := scheduledTx.GetInner().(type) {
				case *types.ArbitrumRetryTx:
					txGasUsed = arbmath.SaturatingUSub(txGasUsed, inner.Gas)
				default:
					log.Warn("Unexpected type of scheduled tx", "type", scheduledTx.Type())
				}
			}
		}

		// Update expectedTotalBalanceDelta (also done in logs loop)
		switch txInner := tx.GetInner().(type) {
		case *types.ArbitrumDepositTx:
			// L1->L2 deposits add eth to the system
			expectedBalanceDelta.Add(expectedBalanceDelta, txInner.Value)
		case *types.ArbitrumSubmitRetryableTx:
			// Retryable submission can include a deposit which adds eth to the system
			expectedBalanceDelta.Add(expectedBalanceDelta, txInner.DepositValue)
		}

		computeUsed := txGasUsed - dataGas
		if txGasUsed < dataGas {
			log.Error("ApplyTransaction() used less gas than it should have", "delta", dataGas-txGasUsed)
			computeUsed = params.TxGas
		} else if computeUsed < params.TxGas {
			computeUsed = params.TxGas
		}

		if txGasUsed > tx.Gas() {
			return nil, nil, fmt.Errorf("ApplyTransaction() used %v more gas than it should have", txGasUsed-tx.Gas())
		}

		// append any scheduled redeems
		redeems = append(redeems, result.ScheduledTxes...)

		for _, txLog := range receipt.Logs {
			if txLog.Address == ArbSysAddress {
				// L2ToL1TransactionEventID is deprecated in upgrade 4, but it should to safe to make this code handle
				// both events ignoring the version.
				// TODO: Remove L2ToL1Transaction handling on next chain reset
				// L2->L1 withdrawals remove eth from the system
				switch txLog.Topics[0] {
				case L2ToL1TransactionEventID:
					event, err := util.ParseL2ToL1TransactionLog(txLog)
					if err != nil {
						log.Error("Failed to parse L2ToL1Transaction log", "err", err)
					} else {
						expectedBalanceDelta.Sub(expectedBalanceDelta, event.Callvalue)
					}
				case L2ToL1TxEventID:
					event, err := util.ParseL2ToL1TxLog(txLog)
					if err != nil {
						log.Error("Failed to parse L2ToL1Tx log", "err", err)
					} else {
						expectedBalanceDelta.Sub(expectedBalanceDelta, event.Callvalue)
					}
				}
			}
		}

		blockGasLeft = arbmath.SaturatingUSub(blockGasLeft, computeUsed)

		complete = append(complete, tx)
		receipts = append(receipts, receipt)

		if isUserTx {
			userTxsProcessed++
		}
	}

	if statedb.IsTxFiltered() {
		return nil, nil, state.ErrArbTxFilter
	}

	if sequencingHooks.BlockFilter != nil {
		if err = sequencingHooks.BlockFilter(header, statedb, complete, receipts); err != nil {
			return nil, nil, err
		}
	}

	binary.BigEndian.PutUint64(header.Nonce[:], delayedMessagesRead)

	log.Info("Finalize block")
	FinalizeBlock(header, complete, statedb, chainConfig)

	// Touch up the block hashes in receipts
	log.Info("New block")
	tmpBlock := types.NewBlock(header, &types.Body{Transactions: complete}, receipts, trie.NewStackTrie(nil))
	blockHash := tmpBlock.Hash()

	for _, receipt := range receipts {
		receipt.BlockHash = blockHash
		for _, txLog := range receipt.Logs {
			txLog.BlockHash = blockHash
		}
	}

	block := types.NewBlock(header, &types.Body{Transactions: complete}, receipts, trie.NewStackTrie(nil))

	if len(block.Transactions()) != len(receipts) {
		return nil, nil, fmt.Errorf("block has %d txes but %d receipts", len(block.Transactions()), len(receipts))
	}

	log.Info("balance delta")
	balanceDelta := statedb.GetUnexpectedBalanceDelta()
	if !arbmath.BigEquals(balanceDelta, expectedBalanceDelta) {
		// Fail if funds have been minted or debug mode is enabled (i.e. this is a test)
		if balanceDelta.Cmp(expectedBalanceDelta) > 0 || chainConfig.DebugMode() {
			return nil, nil, fmt.Errorf("unexpected total balance delta %v (expected %v)", balanceDelta, expectedBalanceDelta)
		}
		// This is a real chain and funds were burnt, not minted, so only log an error and don't panic
		log.Error("Unexpected total balance delta", "delta", balanceDelta, "expected", expectedBalanceDelta)
	}

	log.Info("Return block")
	return block, receipts, nil
}
