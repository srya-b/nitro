package gethexec

import (
    "fmt"
	"errors"
	"time"

    "github.com/ethereum/go-ethereum/common"
    "github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"

    "github.com/offchainlabs/nitro/arbos"
	"github.com/offchainlabs/nitro/arbos/arbosState"
	"github.com/offchainlabs/nitro/arbos/arbostypes"
	"github.com/offchainlabs/nitro/arbutil"
	"github.com/offchainlabs/nitro/cmd/chaininfo"
	"github.com/offchainlabs/nitro/execution"
	"github.com/offchainlabs/nitro/util/sharedmetrics"
)

func (s *ExecutionEngine) sequenceTransactionsWithBlockMutexCustom(header *arbostypes.L1IncomingMessageHeader, txes types.Transactions, hooks *arbos.SequencingHooks, timeboostedTxs map[common.Hash]struct{}) (*types.Block, error) {
	//log.Info("sequenceTransactionsWithBlockMutex")
	lastBlockHeader, err := s.getCurrentHeader()
	if err != nil {
		return nil, err
	}

	statedb, err := s.bc.StateAt(lastBlockHeader.Root)
	if err != nil {
		return nil, err
	}
	lastBlock := s.bc.GetBlock(lastBlockHeader.Hash(), lastBlockHeader.Number.Uint64())
	if lastBlock == nil {
		return nil, errors.New("can't find block for current header")
	}
	//var witness *stateless.Witness
	//if s.bc.GetVMConfig().StatelessSelfValidation {
	//	witness, err = stateless.NewWitness(lastBlock.Header(), s.bc)
	//	if err != nil {
	//		return nil, err
	//	}
	//}
	//statedb.StartPrefetcher("Sequencer", witness)
	//defer statedb.StopPrefetcher()
	statedb.StopPrefetcher()

	delayedMessagesRead := lastBlockHeader.Nonce.Uint64()
	logdir := "/home/user/state-logs"
	statedb.StartLogger(logdir, lastBlockHeader.Number)

	startTime := time.Now()
	block, receipts, err := arbos.ProduceBlockAdvancedCustom(
		header,
		txes,
		delayedMessagesRead,
		lastBlockHeader,
		statedb,
		s.bc,
		hooks,
		false,
		core.MessageCommitMode,
	)
	if err != nil {
		return nil, err
	}

	blockCalcTime := time.Since(startTime)
	blockExecutionTimer.Update(blockCalcTime)
	if len(hooks.TxErrors) != len(txes) {
		return nil, fmt.Errorf("unexpected number of error results: %v vs number of txes %v", len(hooks.TxErrors), len(txes))
	}

	if len(receipts) == 0 {
		return nil, nil
	}

	allTxsErrored := true
	for _, err := range hooks.TxErrors {
		if err == nil {
			allTxsErrored = false
			break
		}
	}
	if allTxsErrored {
		return nil, nil
	}

	//log.Info("[Sequence] message from txs")
	msg, err := MessageFromTxes(header, txes, hooks.TxErrors)
	if err != nil {
		return nil, err
	}

	//log.Info("[Sequence] block number to message")
	msgIdx, err := s.BlockNumberToMessageIndex(lastBlockHeader.Number.Uint64() + 1)
	if err != nil {
		return nil, err
	}

	//log.Info("[Sequence] essage with metadata")
	msgWithMeta := arbostypes.MessageWithMetadata{
		Message:             msg,
		DelayedMessagesRead: delayedMessagesRead,
	}

	//log.Info("[Sequence] result from header")
	msgResult, err := s.resultFromHeader(block.Header())
	if err != nil {
		return nil, err
	}

	//log.Info("[Sequence] block metadata")
	blockMetadata := s.blockMetadataFromBlock(block, timeboostedTxs)
	_, err = s.consensus.WriteMessageFromSequencer(msgIdx, msgWithMeta, *msgResult, blockMetadata).Await(s.GetContext())
	if err != nil {
		return nil, err
	}

	// Only write the block after we've written the messages, so if the node dies in the middle of this,
	// it will naturally recover on startup by regenerating the missing block.
	//log.Info("[Sequence] append blcok")
	err = s.appendBlock(block, statedb, receipts, blockCalcTime)
	if err != nil {
		return nil, err
	}

	//log.Info("[Sequence] cache price")
	s.cacheL1PriceDataOfMsg(msgIdx, receipts, block, false)

	return block, nil
}

func (s *ExecutionEngine) createBlockFromNextMessageCustom(msg *arbostypes.MessageWithMetadata, isMsgForPrefetch bool) (*types.Block, *state.StateDB, types.Receipts, error) {
	log.Info("createBlockFromNextMessageCustom")
	currentHeader := s.bc.CurrentBlock()
	if currentHeader == nil {
		return nil, nil, nil, errors.New("failed to get current block header")
	}

	currentBlock := s.bc.GetBlock(currentHeader.Hash(), currentHeader.Number.Uint64())
	if currentBlock == nil {
		return nil, nil, nil, errors.New("can't find block for current header")
	}

	err := s.bc.RecoverState(currentBlock)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("failed to recover block %v state: %w", currentBlock.Number(), err)
	}

	statedb, err := s.bc.StateAt(currentHeader.Root)
	if err != nil {
		return nil, nil, nil, err
	}
	//var witness *stateless.Witness
	//if s.bc.GetVMConfig().StatelessSelfValidation {
	//	witness, err = stateless.NewWitness(currentBlock.Header(), s.bc)
	//	if err != nil {
	//		return nil, nil, nil, err
	//	}
	//}
	//statedb.StartPrefetcher("TransactionStreamer", witness)
	//defer statedb.StopPrefetcher()	
	statedb.StopPrefetcher()

	runMode := core.MessageCommitMode
	if isMsgForPrefetch {
		runMode = core.MessageReplayMode
	}
	
	logdir := "/home/user/state-logs"
	statedb.StartLogger(logdir, currentHeader.Number)
	block, receipts, err := arbos.ProduceBlockCustom(
		msg.Message,
		msg.DelayedMessagesRead,
		currentHeader,
		statedb,
		s.bc,
		//s.bc.Config(),
		isMsgForPrefetch,
		runMode,
	)
	//log.Info("[create block] total ops", "n", statedb.TotalOps)
	//log.Info("Hashes", "o", len(statedb.OpsCalled()))
	//log.Info("Length", "n", len(statedb.PathsTaken))
	//log.Info("Length", "n", len(staetdb.accounts))
	//log.Info("Length", "n", len(statedb.logs))
	//for i:=0; i < statedb.TotalOps; i++ {
	//	log.Info("Op", "", statedb.OpsCalled[i])
	//	log.Info("Hashes", "", statedb.PathsTaken[i])
	//}

	return block, statedb, receipts, err
}

func (s *ExecutionEngine) digestMessageWithBlockMutexCustom(msgIdxToDigest arbutil.MessageIndex, msg *arbostypes.MessageWithMetadata, msgForPrefetch *arbostypes.MessageWithMetadata) (*execution.MessageResult, error) {
	log.Info("digestMessageWithBlockMutexCustom")
	currentHeader, err := s.getCurrentHeader()
	if err != nil {
		return nil, err
	}
	curMsgIdx, err := s.BlockNumberToMessageIndex(currentHeader.Number.Uint64())
	if err != nil {
		return nil, err
	}
	if curMsgIdx+1 != msgIdxToDigest {
		return nil, fmt.Errorf("wrong message number in digest got %d expected %d", msgIdxToDigest, curMsgIdx+1)
	}

	startTime := time.Now()
	//if s.prefetchBlock && msgForPrefetch != nil {
	//	go func() {
	//		_, _, _, err := s.createBlockFromNextMessage(msgForPrefetch, true)
	//		if err != nil {
	//			return
	//		}
	//	}()
	//}

	block, statedb, receipts, err := s.createBlockFromNextMessageCustom(msg, false)
	if err != nil {
		return nil, err
	}
	blockCalcTime := time.Since(startTime)
	blockExecutionTimer.Update(blockCalcTime)

	err = s.appendBlock(block, statedb, receipts, blockCalcTime)
	if err != nil {
		return nil, err
	}
	s.cacheL1PriceDataOfMsg(msgIdxToDigest, receipts, block, false)

	if time.Now().After(s.nextScheduledVersionCheck) {
		s.nextScheduledVersionCheck = time.Now().Add(time.Minute)
		arbState, err := arbosState.OpenSystemArbosState(statedb, nil, true)
		if err != nil {
			return nil, err
		}
		version, timestampInt, err := arbState.GetScheduledUpgrade()
		if err != nil {
			return nil, err
		}
		var timeUntilUpgrade time.Duration
		var timestamp time.Time
		if timestampInt == 0 {
			// This upgrade will take effect in the next block
			timestamp = time.Now()
		} else {
			// This upgrade is scheduled for the future
			timestamp = time.Unix(int64(timestampInt), 0)
			timeUntilUpgrade = time.Until(timestamp)
		}
		maxSupportedVersion := chaininfo.ArbitrumDevTestChainConfig().ArbitrumChainParams.InitialArbOSVersion
		logLevel := log.Warn
		if timeUntilUpgrade < time.Hour*24 {
			logLevel = log.Error
		}
		if version > maxSupportedVersion {
			logLevel(
				"you need to update your node to the latest version before this scheduled ArbOS upgrade",
				"timeUntilUpgrade", timeUntilUpgrade,
				"upgradeScheduledFor", timestamp,
				"maxSupportedArbosVersion", maxSupportedVersion,
				"pendingArbosUpgradeVersion", version,
			)
		}
	}

	sharedmetrics.UpdateSequenceNumberInBlockGauge(msgIdxToDigest)
	s.latestBlockMutex.Lock()
	s.latestBlock = block
	s.latestBlockMutex.Unlock()
	select {
	case s.newBlockNotifier <- struct{}{}:
	default:
	}

	msgResult, err := s.resultFromHeader(block.Header())
	if err != nil {
		return nil, err
	}
	return msgResult, nil
}

