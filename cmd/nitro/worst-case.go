package main

import (
	"os"
	"fmt"
	_"io"
	_"strings"
	"context"
	"path/filepath"
	"math/big"
	"encoding/json"

	_"github.com/cockroachdb/pebble"
	"github.com/ethereum/go-ethereum/log"
	_"github.com/syndtr/goleveldb/leveldb"
	"github.com/ethereum/go-ethereum/ethdb/pebble"
	"github.com/offchainlabs/nitro/cmd/util/confighelpers"
	"github.com/offchainlabs/nitro/cmd/genericconf"
	"github.com/ethereum/go-ethereum/node"
	flag "github.com/spf13/pflag"
	"github.com/offchainlabs/nitro/cmd/conf"
	"github.com/offchainlabs/nitro/execution/gethexec"
	"github.com/offchainlabs/nitro/util/arbmath"
	"github.com/ethereum/go-ethereum/ethdb"
	_"github.com/ethereum/go-ethereum/ethdb/leveldb"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/offchainlabs/nitro/util/dbutil"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/ethereum/go-ethereum/triedb"
	"github.com/ethereum/go-ethereum/common"
	_"github.com/offchainlabs/nitro/cmd/pruning"
	"github.com/ethereum/go-ethereum/core/tracing"
	"github.com/ethereum/go-ethereum/eth/tracers"
	"github.com/offchainlabs/nitro/cmd/staterecovery"
	"github.com/offchainlabs/nitro/cmd/chaininfo"
	"github.com/ethereum/go-ethereum/rlp"
)

//func printSampleUsage(name string) {
//	fmt.Printf("Sample usage: %s [OPTIONS] \n\n", name)
//	fmt.Printf("Options:\n")
//	fmt.Printf("  --help\n")
//	fmt.Printf("  --dev: Start a default L2-only dev chain\n")
//}

//func main() {
//	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))
//
//	log.Info("Worse case data collector")
//
//	os.Exit(mainImpl())
//
//}

//func closeDb(db io.Closer, name string) {
//	if db != nil {
//		err := db.Close()
//		// unfortunately the freezer db means we can't just use errors.Is
//		if err != nil && !strings.Contains(err.Error(), leveldb.ErrClosed.Error()) && !strings.Contains(err.Error(), pebble.ErrClosed.Error()) {
//			log.Warn("failed to close database on shutdown", "db", name, "err", err)
//		}
//	}
//}

//func main() {
//	os.Exit(mainImpl())
//}

const dbPath = "/home/admin/.arbitrum/arb1/nitro/l2chaindata"
const ancientPath = "/home/admin/.arbitrum/arb1/nitro/l2chaindata/ancient"

func geminiMain() int {
// --- 1. Initialize the Logger ---
	// Set up a logger that prints to the console (stderr by default)
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))

	// 1. Open the chain database. Nitro uses PebbleDB.
	// We open it in read-only mode to prevent any accidental writes.
	db, err := pebble.New(dbPath, 0, 0, "nitro", true, false, nil)
	if err != nil {
		log.Error("Failed to open database: %v", "err", err)
		return 1
	}
	defer db.Close()
	log.Info("Database opened successfully in read-only mode.")

	// Wrap the low-level pebble DB in a higher-level database object that
	// implements the required interfaces (like ethdb.Reader).
	chaindb := rawdb.NewDatabase(db)

	// 2. Get the header of the latest block to find the state root.
	// The state root is the entry point to the state trie for that block.
	headHash := rawdb.ReadHeadHeaderHash(chaindb)
	if headHash == (common.Hash{}) {
		log.Error("Could not find head header hash in database.")
		return 1
	}
	headNumber := rawdb.ReadHeaderNumber(chaindb, headHash)
	if headNumber == nil {
		log.Error("Could not find head block number", "hash", headHash.Hex())
		return 1
	}
	header := rawdb.ReadHeader(chaindb, headHash, *headNumber)
	if header == nil {
		log.Error("Could not read head header", "hash", headHash.Hex())
		return 1
	}

	stateRoot := header.Root
	log.Info("Found latest block", "number", header.Number, "root", stateRoot.Hex())
	log.Info("Starting state traversal using StateDB. This may take a long time...")

	// 3. Create a state.Database and then a state.StateDB.
	// This requires creating a triedb.Database first.
	trieDB := triedb.NewDatabase(chaindb, nil)
	// We pass 'nil' for the snapshot tree as we are not using snapshots here.
	stateDatabase := state.NewDatabase(trieDB, nil)
	sdb, err := state.New(stateRoot, stateDatabase)

	if err != nil {
		log.Error("Failed to create StateDB", "err", err)
	}

	// 4. Manually iterate the state trie since ForEach does not exist.
	// We get the underlying trie and create a new iterator.
	t := sdb.GetTrie()
	nodeIterator, err := t.NodeIterator([]byte{})
	if err != nil {
		log.Error("Failed to get node iterator", "err", err)
		return 1
	}
	it := trie.NewIterator(nodeIterator)

	count := 0
	for it.Next() {
		if count > 5 {
			break
		}

		// The iterator key is the sha3 hash of the address, not the address itself.
		hashedAddress := common.BytesToHash(it.Key)

		// The value is the RLP-encoded account data. We need to decode it.
		var acc types.StateAccount
		if err := rlp.DecodeBytes(it.Value, &acc); err != nil {
			log.Error("Failed to decode account.", "key", it.Key, "err", err)
			continue
		}

		fmt.Printf(
			"  - Account %d: [Hashed Address: %s] | Nonce: %d | Balance: %s | CodeHash: %x | StorageRoot: %s\n",
			count,
			hashedAddress.Hex(),
			acc.Nonce,
			acc.Balance.String(),
			acc.CodeHash,
			acc.Root.Hex(),
		)

		// If the account has a non-empty storage root, traverse its storage trie.
		if acc.Root != (common.Hash{}) {
			fmt.Println("    Found Storage Trie. Traversing...")

			// Create a new trie object for the account's storage using its root hash
			// and the same underlying database.
			storageTrie, err := triedb.New(acc.Root, trieDB)
			if err != nil {
				log.Info("    Error creating storage trie", "account", hashedAddress.Hex(), "err", err)
				continue
			}

			// Create an iterator for the storage trie.
			storageNodeIterator, err := storageTrie.NodeIterator([]byte{})
			if err != nil {
				log.Info("    Error getting storage node iterator", "account", hashedAddress.Hex(), "err", err)
				continue
			}
			storageIt := triedb.NewIterator(storageNodeIterator)
			storageCount := 0
			for storageIt.Next() {
				if storageCount > 0 {
					break
				}
				// The key is the hashed storage slot, the value is the RLP-encoded storage value.
				hashedSlot := common.BytesToHash(storageIt.Key)
				// The value is RLP encoded, but for storage it's often just the bytes themselves.
				// We will print the raw bytes as hex.
				fmt.Printf("      -> Slot %d: [Hashed Key: %s] | Value: %x\n", storageCount, hashedSlot.Hex(), storageIt.Value)
				storageCount++
			}
			if storageIt.Err != nil {
				log.Info("    Storage trie iteration failed", "acount", hashedAddress.Hex(), "err", storageIt.Err)
			}
			if storageCount == 0 {
				fmt.Println("    Storage Trie is present but contains no entries.")
			}
		}

		count++
	}
	if it.Err != nil {
		log.Error("Trie iteration failed", "err", it.Err)
		return 1
	}

	log.Info("Traversak complete.", "total accounts", count)


	return 0
}

// Returns the exit code
func worstCase() int {
	
	log.SetDefault(log.NewLogger(log.NewTerminalHandlerWithLevel(os.Stderr, log.LevelDebug, true)))

	log.Info("Worse case data collector")

	ctx, cancelFunc := context.WithCancel(context.Background())
	defer cancelFunc()

	args := os.Args[1:]
	nodeConfig, _, err := ParseNode(ctx, args)
	if err != nil {
		confighelpers.PrintErrorAndExit(err, printSampleUsage)
	}
	stackConf := node.DefaultConfig
	stackConf.DataDir = nodeConfig.Persistent.Chain
	stackConf.DBEngine = nodeConfig.Persistent.DBEngine
	nodeConfig.Rpc.Apply(&stackConf)
	nodeConfig.HTTP.Apply(&stackConf)
	nodeConfig.WS.Apply(&stackConf)
	nodeConfig.Auth.Apply(&stackConf)
	nodeConfig.IPC.Apply(&stackConf)
	nodeConfig.GraphQL.Apply(&stackConf)
	stackConf.P2P.ListenAddr = ""
	stackConf.P2P.NoDial = true
	stackConf.P2P.NoDiscovery = true
	_, strippedRevision, _ := confighelpers.GetVersion()
	stackConf.Version = strippedRevision

	pathResolver := func(workdir string) func(string) string {
		if workdir == "" {
			workdir, err = os.Getwd()
			if err != nil {
				log.Warn("Failed to get workdir", "err", err)
			}
		}
		return func(path string) string {
			if filepath.IsAbs(path) {
				return path
			}
			return filepath.Join(workdir, path)
		}
	}

	if stackConf.JWTSecret == "" && stackConf.AuthAddr != "" {
		filename := pathResolver(nodeConfig.Persistent.GlobalConfig)("jwtsecret")
		if err := genericconf.TryCreatingJWTSecret(filename); err != nil {
			log.Error("Failed to prepare jwt secret file", "err", err)
			return 1
		}
		stackConf.JWTSecret = filename
	}
	err = genericconf.InitLog(nodeConfig.LogType, nodeConfig.LogLevel, &nodeConfig.FileLogging, pathResolver(nodeConfig.Persistent.LogDir))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error initializing logging: %v\n", err)
		return 1
	}

	stack, err := node.New(&stackConf)
	if err != nil {
		flag.Usage()
		log.Crit("failed to initialize geth stack", "err", err)
	}

	var deferFuncs []func()
	defer func() {
		for i := range deferFuncs {
			deferFuncs[i]()
		}
	}()


	traceConfig := nodeConfig.Execution.VmTrace
	var tracer *tracing.Hooks
	if traceConfig.TracerName != "" {
		tracer, err = tracers.LiveDirectory.New(traceConfig.TracerName, json.RawMessage(traceConfig.JSONConfig))
		if err != nil {
			log.Error("custom tracer error:", "name", traceConfig.TracerName, "err", err)
			return 1
		}
		log.Info("enabling custom tracer", "name", traceConfig.TracerName)
	}

	//_, _, err = openTestChainDb(ctx,  stack, new(big.Int).SetUint64(nodeConfig.Chain.ID), nodeConfig, &nodeConfig.Persistent, &nodeConfig.Execution.StylusTarget, gethexec.DefaultCacheConfigFor(stack, &nodeConfig.Execution.Caching))	
	chainDb, l2BlockChain, err := openTestChainDb(ctx, stack, nodeConfig, new(big.Int).SetUint64(nodeConfig.Chain.ID), gethexec.DefaultCacheConfigFor(&nodeConfig.Execution.Caching), &nodeConfig.Execution.StylusTarget, tracer, &nodeConfig.Persistent)
	if err != nil {
		log.Error("open test chain db error", "err", err)
		return 1
	}
	if l2BlockChain != nil {
		deferFuncs = append(deferFuncs, func() { l2BlockChain.Stop() })
	}
	deferFuncs = append(deferFuncs, func() { closeDb(chainDb, "chainDb") })
	if err != nil {
		flag.Usage()
		log.Error("error initializing database", "err", err)
		return 1
	}

	chainInfo, err := chaininfo.ProcessChainInfo(nodeConfig.Chain.ID, nodeConfig.Chain.Name, nodeConfig.Chain.InfoFiles, nodeConfig.Chain.InfoJson)
	if err != nil {
		log.Error("error processing l2 chain info", "err", err)
		return 1
	}
	if err := validateBlockChain(l2BlockChain, chainInfo.ChainConfig); err != nil {
		log.Error("user provided chain config is not compatible with onchain chain config", "err", err)
		return 1
	}

	// try to open blockchain and get the header root
	currentBlock := l2BlockChain.CurrentBlock()
	if currentBlock == nil {
		log.Error("Couldn't get current block")
		return 1
	}
	log.Info("Current block header", "h", currentBlock.Root)

	return 0
}


//func openTestChainDb(ctx context.Context, stack *node.Node, config *NodeConfig, chainId *big.Int, cacheConfig *core.CacheConfig, targetConfig *gethexec.StylusTargetConfig, tracer *tracing.Hooks, persistentConfig *conf.PersistentConfig, l1Client *ethclient.Client, rollupAddrs chaininfo.RollupAddresses) (ethdb.Database, *core.BlockChain, error) {
func openTestChainDb(ctx context.Context, stack *node.Node, config *NodeConfig, chainId *big.Int, cacheConfig *core.CacheConfig, targetConfig *gethexec.StylusTargetConfig, tracer *tracing.Hooks, persistentConfig *conf.PersistentConfig) (ethdb.Database, *core.BlockChain, error) {
	if !config.Init.Force {
		if readOnlyDb, err := stack.OpenDatabaseWithFreezerWithExtraOptions("l2chaindata", 0, 0, config.Persistent.Ancient, "l2chaindata/", true, persistentConfig.Pebble.ExtraOptions("l2chaindata")); err == nil {
			if chainConfig := gethexec.TryReadStoredChainConfig(readOnlyDb); chainConfig != nil {
				readOnlyDb.Close()
				log.Info("Close read only db and do the rest")
				if !arbmath.BigEquals(chainConfig.ChainID, chainId) {
					return nil, nil, fmt.Errorf("database has chain ID %v but config has chain ID %v (are you sure this database is for the right chain?)", chainConfig.ChainID, chainId)
				}
				chainData, err := stack.OpenDatabaseWithFreezerWithExtraOptions("l2chaindata", config.Execution.Caching.DatabaseCache, config.Persistent.Handles, config.Persistent.Ancient, "l2chaindata/", false, persistentConfig.Pebble.ExtraOptions("l2chaindata"))
				if err != nil {
					return nil, nil, err
				}
				if err := dbutil.UnfinishedConversionCheck(chainData); err != nil {
					return nil, nil, fmt.Errorf("l2chaindata unfinished database conversion check error: %w", err)
				}
				wasmDb, err := stack.OpenDatabaseWithExtraOptions("wasm", config.Execution.Caching.DatabaseCache, config.Persistent.Handles, "wasm/", false, persistentConfig.Pebble.ExtraOptions("wasm"))
				if err != nil {
					return nil, nil, err
				}
				if err := validateOrUpgradeWasmStoreSchemaVersion(wasmDb); err != nil {
					return nil, nil, err
				}
				if err := validateOrUpgradeWasmerSerializeVersion(wasmDb); err != nil {
					return nil, nil, err
				}
				if err := dbutil.UnfinishedConversionCheck(wasmDb); err != nil {
					return nil, nil, fmt.Errorf("wasm unfinished database conversion check error: %w", err)
				}
				chainDb := rawdb.WrapDatabaseWithWasm(chainData, wasmDb)
				_, err = rawdb.ParseStateScheme(cacheConfig.StateScheme, chainDb)
				if err != nil {
					return nil, nil, err
				}
				//err = pruning.PruneChainDb(ctx, chainDb, stack, &config.Init, cacheConfig, persistentConfig, l1Client, rollupAddrs, config.Node.ValidatorRequired())
				//if err != nil {
				//	return chainDb, nil, fmt.Errorf("error pruning: %w", err)
				//}
				l2BlockChain, err := gethexec.GetBlockChain(chainDb, cacheConfig, chainConfig, tracer, &config.Execution.TxIndexer)
				if err != nil {
					return chainDb, nil, err
				}
				err = validateBlockChain(l2BlockChain, chainConfig)
				if err != nil {
					return chainDb, l2BlockChain, err
				}
				if config.Init.RecreateMissingStateFrom > 0 {
					err = staterecovery.RecreateMissingStates(chainDb, l2BlockChain, cacheConfig, config.Init.RecreateMissingStateFrom)
					if err != nil {
						return chainDb, l2BlockChain, fmt.Errorf("failed to recreate missing states: %w", err)
					}
				}
				return rebuildLocalWasm(ctx, &config.Execution, l2BlockChain, chainDb, wasmDb, config.Init.RebuildLocalWasm)
			}
			log.Error("Just closed readOnlyDb didn't get chain config")
			readOnlyDb.Close()
		} else if !dbutil.IsNotExistError(err) {
			// we only want to continue if the database does not exist
			log.Error("Couldn't even open the readOnlyDb (is not exist)")
			return nil, nil, fmt.Errorf("Failed to open database: %w", err)
		} else {
			log.Error("Some other error with the database", "err", err)
		}
	}

	return nil, nil, fmt.Errorf("Database exists but read chain config failed to it closed")

	//// Check if database was misplaced in parent dir
	//const errorFmt = "database was not found in %s, but it was found in %s (have you placed the database in the wrong directory?)"
	//parentDir := filepath.Dir(stack.InstanceDir())
	//if dirExists(path.Join(parentDir, "l2chaindata")) {
	//	return nil, nil, fmt.Errorf(errorFmt, stack.InstanceDir(), parentDir)
	//}
	//grandParentDir := filepath.Dir(parentDir)
	//if dirExists(path.Join(grandParentDir, "l2chaindata")) {
	//	return nil, nil, fmt.Errorf(errorFmt, stack.InstanceDir(), grandParentDir)
	//}

	//if err := checkEmptyDatabaseDir(stack.InstanceDir(), config.Init.Force); err != nil {
	//	return nil, nil, err
	//}

	//if err := setLatestSnapshotUrl(ctx, &config.Init, config.Chain.Name); err != nil {
	//	return nil, nil, err
	//}

	//initFile, cleanUpTmp, err := initializeAndDownloadInit(ctx, &config.Init, stack)
	//defer cleanUpTmp()
	//if err != nil {
	//	return nil, nil, err
	//}

	//if initFile != "" {
	//	if err := extractSnapshot(initFile, stack.InstanceDir(), config.Init.ImportWasm); err != nil {
	//		return nil, nil, err
	//	}
	//}

	//var initDataReader statetransfer.InitDataReader = nil

	//chainData, err := stack.OpenDatabaseWithFreezerWithExtraOptions("l2chaindata", config.Execution.Caching.DatabaseCache, config.Persistent.Handles, config.Persistent.Ancient, "l2chaindata/", false, persistentConfig.Pebble.ExtraOptions("l2chaindata"))
	//if err != nil {
	//	return nil, nil, err
	//}
	//wasmDb, err := stack.OpenDatabaseWithExtraOptions("wasm", config.Execution.Caching.DatabaseCache, config.Persistent.Handles, "wasm/", false, persistentConfig.Pebble.ExtraOptions("wasm"))
	//if err != nil {
	//	return nil, nil, err
	//}
	//if err := validateOrUpgradeWasmStoreSchemaVersion(wasmDb); err != nil {
	//	return nil, nil, err
	//}
	//chainDb := rawdb.WrapDatabaseWithWasm(chainData, wasmDb)
	//_, err = rawdb.ParseStateScheme(cacheConfig.StateScheme, chainDb)
	//if err != nil {
	//	return nil, nil, err
	//}

	//// Rebuilding wasm store is not required when just starting out
	//err = gethexec.WriteToKeyValueStore(wasmDb, gethexec.RebuildingPositionKey, gethexec.RebuildingDone)
	//log.Info("Setting codehash position in rebuilding of wasm store to done")
	//if err != nil {
	//	return nil, nil, fmt.Errorf("unable to set codehash position in rebuilding of wasm store to done: %w", err)
	//}

	//if config.Init.ImportFile != "" {
	//	initDataReader, err = statetransfer.NewJsonInitDataReader(config.Init.ImportFile)
	//	if err != nil {
	//		return chainDb, nil, fmt.Errorf("error reading import file: %w", err)
	//	}
	//}
	//if config.Init.Empty {
	//	if initDataReader != nil {
	//		return chainDb, nil, errors.New("multiple init methods supplied")
	//	}
	//	initData := statetransfer.ArbosInitializationInfo{
	//		NextBlockNumber: 0,
	//	}
	//	initDataReader = statetransfer.NewMemoryInitDataReader(&initData)
	//}
	//if config.Init.DevInit {
	//	if initDataReader != nil {
	//		return chainDb, nil, errors.New("multiple init methods supplied")
	//	}
	//	initData := statetransfer.ArbosInitializationInfo{
	//		NextBlockNumber: config.Init.DevInitBlockNum,
	//		Accounts: []statetransfer.AccountInitializationInfo{
	//			{
	//				Addr:       common.HexToAddress(config.Init.DevInitAddress),
	//				EthBalance: new(big.Int).Mul(big.NewInt(params.Ether), big.NewInt(1000)),
	//				Nonce:      0,
	//			},
	//		},
	//		ChainOwner: common.HexToAddress(config.Init.DevInitAddress),
	//	}
	//	initDataReader = statetransfer.NewMemoryInitDataReader(&initData)
	//}

	//var chainConfig *params.ChainConfig
	//var genesisArbOSInit *params.ArbOSInit

	//if config.Init.GenesisJsonFile != "" {
	//	if initDataReader != nil {
	//		return chainDb, nil, errors.New("multiple init methods supplied")
	//	}
	//	genesisJson, err := os.ReadFile(config.Init.GenesisJsonFile)
	//	if err != nil {
	//		return chainDb, nil, err
	//	}
	//	var gen core.Genesis
	//	if err := json.Unmarshal(genesisJson, &gen); err != nil {
	//		return chainDb, nil, err
	//	}
	//	var accounts []statetransfer.AccountInitializationInfo
	//	for address, account := range gen.Alloc {
	//		accounts = append(accounts, statetransfer.AccountInitializationInfo{
	//			Addr:       address,
	//			EthBalance: account.Balance,
	//			Nonce:      account.Nonce,
	//			ContractInfo: &statetransfer.AccountInitContractInfo{
	//				Code:            account.Code,
	//				ContractStorage: account.Storage,
	//			},
	//		})
	//	}
	//	initDataReader = statetransfer.NewMemoryInitDataReader(&statetransfer.ArbosInitializationInfo{
	//		Accounts: accounts,
	//	})
	//	chainConfig = gen.Config
	//	genesisArbOSInit = gen.ArbOSInit
	//}

	//var l2BlockChain *core.BlockChain
	//txIndexWg := sync.WaitGroup{}
	//if initDataReader == nil {
	//	chainConfig = gethexec.TryReadStoredChainConfig(chainDb)
	//	if chainConfig == nil {
	//		return chainDb, nil, errors.New("no --init.* mode supplied and chain data not in expected directory")
	//	}
	//	l2BlockChain, err = gethexec.GetBlockChain(chainDb, cacheConfig, chainConfig, tracer, &config.Execution.TxIndexer)
	//	if err != nil {
	//		return chainDb, nil, err
	//	}
	//	genesisBlockNr := chainConfig.ArbitrumChainParams.GenesisBlockNum
	//	genesisBlock := l2BlockChain.GetBlockByNumber(genesisBlockNr)
	//	if genesisBlock != nil {
	//		log.Info("loaded genesis block from database", "number", genesisBlockNr, "hash", genesisBlock.Hash())
	//	} else {
	//		// The node will probably die later, but might as well not kill it here?
	//		log.Error("database missing genesis block", "number", genesisBlockNr)
	//	}
	//	testUpdateTxIndex(chainDb, chainConfig, &txIndexWg)
	//} else {
	//	genesisBlockNr, err := initDataReader.GetNextBlockNumber()
	//	if err != nil {
	//		return chainDb, nil, err
	//	}
	//	if chainConfig == nil {
	//		chainConfig, err = chaininfo.GetChainConfig(new(big.Int).SetUint64(config.Chain.ID), config.Chain.Name, genesisBlockNr, config.Chain.InfoFiles, config.Chain.InfoJson)
	//		if err != nil {
	//			return chainDb, nil, err
	//		}
	//	}
	//	if config.Init.DevInit && config.Init.DevMaxCodeSize != 0 {
	//		chainConfig.ArbitrumChainParams.MaxCodeSize = config.Init.DevMaxCodeSize
	//	}
	//	testUpdateTxIndex(chainDb, chainConfig, &txIndexWg)
	//	ancients, err := chainDb.Ancients()
	//	if err != nil {
	//		return chainDb, nil, err
	//	}
	//	if ancients < genesisBlockNr {
	//		return chainDb, nil, fmt.Errorf("%v pre-init blocks required, but only %v found", genesisBlockNr, ancients)
	//	}
	//	if ancients > genesisBlockNr {
	//		storedGenHash := rawdb.ReadCanonicalHash(chainDb, genesisBlockNr)
	//		storedGenBlock := rawdb.ReadBlock(chainDb, storedGenHash, genesisBlockNr)
	//		if storedGenBlock.Header().Root == (common.Hash{}) {
	//			return chainDb, nil, fmt.Errorf("attempting to init genesis block %x, but this block is in database with no state root", genesisBlockNr)
	//		}
	//		log.Warn("Re-creating genesis though it seems to exist in database", "blockNr", genesisBlockNr)
	//	}
	//	log.Info("Initializing", "ancients", ancients, "genesisBlockNr", genesisBlockNr)
	//	if config.Init.ThenQuit {
	//		cacheConfig.SnapshotWait = true
	//	}
	//	var parsedInitMessage *arbostypes.ParsedInitMessage
	//	if config.Node.ParentChainReader.Enable {
	//		delayedBridge, err := arbnode.NewDelayedBridge(l1Client, rollupAddrs.Bridge, rollupAddrs.DeployedAt)
	//		if err != nil {
	//			return chainDb, nil, fmt.Errorf("failed creating delayed bridge while attempting to get serialized chain config from init message: %w", err)
	//		}
	//		deployedAt := new(big.Int).SetUint64(rollupAddrs.DeployedAt)
	//		delayedMessages, err := delayedBridge.LookupMessagesInRange(ctx, deployedAt, deployedAt, nil)
	//		if err != nil {
	//			return chainDb, nil, fmt.Errorf("failed getting delayed messages while attempting to get serialized chain config from init message: %w", err)
	//		}
	//		var initMessage *arbostypes.L1IncomingMessage
	//		for _, msg := range delayedMessages {
	//			if msg.Message.Header.Kind == arbostypes.L1MessageType_Initialize {
	//				initMessage = msg.Message
	//				break
	//			}
	//		}
	//		if initMessage == nil {
	//			return chainDb, nil, fmt.Errorf("failed to get init message while attempting to get serialized chain config")
	//		}
	//		parsedInitMessage, err = initMessage.ParseInitMessage()
	//		if err != nil {
	//			return chainDb, nil, err
	//		}
	//		if parsedInitMessage.ChainId.Cmp(chainId) != 0 {
	//			return chainDb, nil, fmt.Errorf("expected L2 chain ID %v but read L2 chain ID %v from init message in L1 inbox", chainId, parsedInitMessage.ChainId)
	//		}
	//		if parsedInitMessage.ChainConfig != nil {
	//			if err := parsedInitMessage.ChainConfig.CheckCompatible(chainConfig, chainConfig.ArbitrumChainParams.GenesisBlockNum, 0); err != nil {
	//				return chainDb, nil, fmt.Errorf("incompatible chain config read from init message in L1 inbox: %w", err)
	//			}
	//		}
	//		log.Info("Read serialized chain config from init message", "json", string(parsedInitMessage.SerializedChainConfig))
	//	} else {
	//		serializedChainConfig, err := json.Marshal(chainConfig)
	//		if err != nil {
	//			return chainDb, nil, err
	//		}
	//		parsedInitMessage = &arbostypes.ParsedInitMessage{
	//			ChainId:               chainConfig.ChainID,
	//			InitialL1BaseFee:      arbostypes.DefaultInitialL1BaseFee,
	//			ChainConfig:           chainConfig,
	//			SerializedChainConfig: serializedChainConfig,
	//		}
	//		log.Warn("Created fake init message as L1Reader is disabled and serialized chain config from init message is not available", "json", string(serializedChainConfig))
	//	}

	//	emptyBlockChain := rawdb.ReadHeadHeader(chainDb) == nil
	//	if !emptyBlockChain && (cacheConfig.StateScheme == rawdb.PathScheme) && config.Init.Force {
	//		return chainDb, nil, errors.New("It is not possible to force init with non-empty blockchain when using path scheme")
	//	}
	//	l2BlockChain, err = gethexec.WriteOrTestBlockChain(chainDb, cacheConfig, initDataReader, chainConfig, genesisArbOSInit, tracer, parsedInitMessage, &config.Execution.TxIndexer, config.Init.AccountsPerSync)
	//	if err != nil {
	//		return chainDb, nil, err
	//	}
	//}

	//txIndexWg.Wait()
	//err = chainDb.Sync()
	//if err != nil {
	//	return chainDb, l2BlockChain, err
	//}

	//err = pruning.PruneChainDb(ctx, chainDb, stack, &config.Init, cacheConfig, persistentConfig, l1Client, rollupAddrs, config.Node.ValidatorRequired())
	//if err != nil {
	//	return chainDb, nil, fmt.Errorf("error pruning: %w", err)
	//}

	//err = validateBlockChain(l2BlockChain, chainConfig)
	//if err != nil {
	//	return chainDb, l2BlockChain, err
	//}

	//return rebuildLocalWasm(ctx, &config.Execution, l2BlockChain, chainDb, wasmDb, config.Init.RebuildLocalWasm)
}

