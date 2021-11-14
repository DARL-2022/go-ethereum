// Copyright 2014 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package vm

import (
	// (joonha)
	"bytes" 
	// "encoding/binary"
	// "fmt"

	"errors"
	"math/big"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
	"github.com/holiman/uint256"


	// (joonha)
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/trie"
	"github.com/ethereum/go-ethereum/core/rawdb"
)

// emptyCodeHash is used by create to ensure deployment is disallowed to already
// deployed contract addresses (relevant after the account abstraction).
var emptyCodeHash = crypto.Keccak256Hash(nil)

type (
	// CanTransferFunc is the signature of a transfer guard function
	CanTransferFunc func(StateDB, common.Address, *big.Int) bool
	// TransferFunc is the signature of a transfer function
	TransferFunc func(StateDB, common.Address, common.Address, *big.Int)
	// Restore function should be defined here (joonha) (ethane)
	// RestoreFunc is the signature of a restore function (jmlee)
	RestoreFunc func(StateDB, common.Address, *big.Int, *big.Int)
	// GetHashFunc returns the n'th block hash in the blockchain
	// and is used by the BLOCKHASH EVM op code.
	GetHashFunc func(uint64) common.Hash

)

func (evm *EVM) precompile(addr common.Address) (PrecompiledContract, bool) {
	var precompiles map[common.Address]PrecompiledContract
	switch {
	case evm.chainRules.IsBerlin:
		precompiles = PrecompiledContractsBerlin
	case evm.chainRules.IsIstanbul:
		precompiles = PrecompiledContractsIstanbul
	case evm.chainRules.IsByzantium:
		precompiles = PrecompiledContractsByzantium
	default:
		precompiles = PrecompiledContractsHomestead
	}
	p, ok := precompiles[addr]
	return p, ok
}

// run runs the given contract and takes care of running precompiles with a fallback to the byte code interpreter.
func run(evm *EVM, contract *Contract, input []byte, readOnly bool) ([]byte, error) {
	for _, interpreter := range evm.interpreters {
		if interpreter.CanRun(contract.Code) {
			if evm.interpreter != interpreter {
				// Ensure that the interpreter pointer is set back
				// to its current value upon return.
				defer func(i Interpreter) {
					evm.interpreter = i
				}(evm.interpreter)
				evm.interpreter = interpreter
			}
			return interpreter.Run(contract, input, readOnly)
		}
	}
	return nil, errors.New("no compatible interpreter")
}

// BlockContext provides the EVM with auxiliary information. Once provided
// it shouldn't be modified.
type BlockContext struct {
	// CanTransfer returns whether the account contains
	// sufficient ether to transfer the value
	CanTransfer CanTransferFunc
	// Transfer transfers ether from one account to the other
	Transfer TransferFunc
	// Restore function should be defined here (joonha) (ethane)
	Restore RestoreFunc
	// GetHash returns the hash corresponding to n
	GetHash GetHashFunc

	// Block information
	Coinbase    common.Address // Provides information for COINBASE
	GasLimit    uint64         // Provides information for GASLIMIT
	BlockNumber *big.Int       // Provides information for NUMBER
	Time        *big.Int       // Provides information for TIME
	Difficulty  *big.Int       // Provides information for DIFFICULTY
}

// TxContext provides the EVM with information about a transaction.
// All fields can change between transactions.
type TxContext struct {
	// Message information
	Origin   common.Address // Provides information for ORIGIN
	GasPrice *big.Int       // Provides information for GASPRICE
}

// EVM is the Ethereum Virtual Machine base object and provides
// the necessary tools to run a contract on the given state with
// the provided context. It should be noted that any error
// generated through any of the calls should be considered a
// revert-state-and-consume-all-gas operation, no checks on
// specific errors should ever be performed. The interpreter makes
// sure that any errors generated are to be considered faulty code.
//
// The EVM should never be reused and is not thread safe.
type EVM struct {
	// Context provides auxiliary blockchain related information
	Context BlockContext
	TxContext
	// StateDB gives access to the underlying state
	StateDB StateDB
	// Depth is the current call stack
	depth int

	// chainConfig contains information about the current chain
	chainConfig *params.ChainConfig
	// chain rules contains the chain rules for the current epoch
	chainRules params.Rules
	// virtual machine configuration options used to initialise the
	// evm.
	vmConfig Config
	// global (to this context) ethereum virtual machine
	// used throughout the execution of the tx.
	interpreters []Interpreter
	interpreter  Interpreter
	// abort is used to abort the EVM calling operations
	// NOTE: must be set atomically
	abort int32
	// callGasTemp holds the gas available for the current call. This is needed because the
	// available gas is calculated in gasCall* according to the 63/64 rule and later
	// applied in opCall*.
	callGasTemp uint64
}

// NewEVM returns a new EVM. The returned EVM is not thread safe and should
// only ever be used *once*.
func NewEVM(blockCtx BlockContext, txCtx TxContext, statedb StateDB, chainConfig *params.ChainConfig, vmConfig Config) *EVM {
	evm := &EVM{
		Context:      blockCtx,
		TxContext:    txCtx,
		StateDB:      statedb,
		vmConfig:     vmConfig,
		chainConfig:  chainConfig,
		chainRules:   chainConfig.Rules(blockCtx.BlockNumber),
		interpreters: make([]Interpreter, 0, 1),
	}

	if chainConfig.IsEWASM(blockCtx.BlockNumber) {
		// to be implemented by EVM-C and Wagon PRs.
		// if vmConfig.EWASMInterpreter != "" {
		//  extIntOpts := strings.Split(vmConfig.EWASMInterpreter, ":")
		//  path := extIntOpts[0]
		//  options := []string{}
		//  if len(extIntOpts) > 1 {
		//    options = extIntOpts[1..]
		//  }
		//  evm.interpreters = append(evm.interpreters, NewEVMVCInterpreter(evm, vmConfig, options))
		// } else {
		// 	evm.interpreters = append(evm.interpreters, NewEWASMInterpreter(evm, vmConfig))
		// }
		panic("No supported ewasm interpreter yet.")
	}

	// vmConfig.EVMInterpreter will be used by EVM-C, it won't be checked here
	// as we always want to have the built-in EVM as the failover option.
	evm.interpreters = append(evm.interpreters, NewEVMInterpreter(evm, vmConfig))
	evm.interpreter = evm.interpreters[0]

	return evm
}

// Reset resets the EVM with a new transaction context.Reset
// This is not threadsafe and should only be done very cautiously.
func (evm *EVM) Reset(txCtx TxContext, statedb StateDB) {
	evm.TxContext = txCtx
	evm.StateDB = statedb
}

// Cancel cancels any running EVM operation. This may be called concurrently and
// it's safe to be called multiple times.
func (evm *EVM) Cancel() {
	atomic.StoreInt32(&evm.abort, 1)
}

// Cancelled returns true if Cancel has been called
func (evm *EVM) Cancelled() bool {
	return atomic.LoadInt32(&evm.abort) == 1
}

// Interpreter returns the current interpreter
func (evm *EVM) Interpreter() Interpreter {
	return evm.interpreter
}

// Call executes the contract associated with the addr with the given input as
// parameters. It also handles any necessary value transfer required and takes
// the necessary steps to create accounts and reverses the state in case of an
// execution error or failed value transfer.
func (evm *EVM) Call(caller ContractRef, addr common.Address, input []byte, gas uint64, value *big.Int) (ret []byte, leftOverGas uint64, err error) {

	log.Info("CALLL IS CALLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLED") // (joonha)

	if evm.vmConfig.NoRecursion && evm.depth > 0 {
		return nil, gas, nil
	}
	// Fail if we're trying to execute above the call depth limit
	if evm.depth > int(params.CallCreateDepth) {
		return nil, gas, ErrDepth
	}
	// Fail if we're trying to transfer more than the available balance
	if value.Sign() != 0 && !evm.Context.CanTransfer(evm.StateDB, caller.Address(), value) {
		return nil, gas, ErrInsufficientBalance
	}
	snapshot := evm.StateDB.Snapshot()
	p, isPrecompile := evm.precompile(addr)

	// (joonha) is commenting out to fix 0123~789 account being added to trie
	if !evm.StateDB.Exist(addr) {
		if !isPrecompile && evm.chainRules.IsEIP158 && value.Sign() == 0 {
			// Calling a non existing account, don't do anything, but ping the tracer
			if evm.vmConfig.Debug && evm.depth == 0 {
				evm.vmConfig.Tracer.CaptureStart(evm, caller.Address(), addr, false, input, gas, value)
				evm.vmConfig.Tracer.CaptureEnd(ret, 0, 0, nil)
			}
			return nil, gas, nil
		}
		// evm.StateDB.CreateAccount(addr)
	}


	// (joonha)
	/***************************************/
	// ETHANE RESTORATION
	/***************************************/
	// if 문을 추가하여 restoration을 구현한 것이 ethanos임.
	// 이때 아랫줄 evm.Context.Transfer(evm.StateDB ~~~ 이 부분이 else 문으로 들어갔음.
	// 즉 기존 geth의 검색 범위에서 해당하는 account가 발견되지 않으면 restoration을 수행하는 것을
	// if 문에 넣어야 하고, 그렇지 않은 (account가 발견된) 경우 아래의 원래 코드를 수행하는 것을
	// else 문에 넣어야 함.

	if addr == common.HexToAddress("0x0123456789012345678901234567890123456789") { // restoration

		common.Restoring = 1 // restoration starts

		log.Info("\n")

		/***************************************/
		// MEMO
		/***************************************/
		// tx 데이터를 data에 넣는다.
		// data의 첫째 요소가 tx에서 복구하고자 하는 inactive account의 address다.
		// 가장 최근의 inactive account를 복구한다.


		/***************************************/
		// NOTATIONS
		/***************************************/
		// data: Restore Tx
		// cnt: counter to refer to the Tx data instances
		// limit: number of Tx data instances
		// inactiveAddr: account addr to restore
		// inactiveKey: account key to restore (in the inactive trie)
		// blockNum: restoration target's block number
		// checkpointBlock: same as blockNum
		// accounts: list of accounts to be restored

		
		/***************************************/
		// CHECK
		/***************************************/
		// 1. accounts로 목록을 만들어야 하는지 vs. account 하나만 있으면 되는지.
		// 애초에 restore tx 내용에 여러 node에 대한 restore 요청이 들어올 것이다. 
		// 그러므로 accounts 목록을 두는 것이 좋겠다.
		// 단 Ethanos와 달리 한 state에서만 list의 모든 account를 탐색하면 된다.
		// >> 변경: account 하나에 대한 restore만을 하나의 tx에 담는다.
		//         그리고 가장 우측(가장 최근) account를 restore 한다.
		//         즉 addrToKey_inactivate 중 가장 최근 key를 참조하면 된다.
		//         이걸 여기서 하면 됨.
		//         즉 account 목록이 아니라 하나만 두면 됨!
		//         그런데 account 목록에 하나만 있는 것은 문제가 되지 않으니까 리스트는 그대로 두겠음.
		//
		// 2. restore 후 inactive trie에서 account를 nil로 변경해줘야 함.
		

		// decode rlp encoded data
		var data []interface{}
		rlp.Decode(bytes.NewReader(input), &data)
		log.Info("### print input decode", "data", data)

		cnt := 0
		limit := len(data)

		if limit == 0 {
			// Error: no proof in tx data
			log.Info("Restore Error: no proof in tx data")
			return nil, gas, ErrInvalidProof
		}

		// get inactive account address
		inactiveAddrString := string(data[cnt].([]byte))
		inactiveAddr := common.HexToAddress(inactiveAddrString)
		
		// get latest key from addrToKey_inactive 
		if common.AddrToKey_inactive[inactiveAddr] == nil{
			log.Info("### flag 0")
		}
		
		log.Info("### restoration target", "address", inactiveAddr)
		log.Info("### len(AddrToKey_inactive)", "len(AddrToKey_inactive)", len(common.AddrToKey_inactive[inactiveAddr]))
		log.Info("### AddrToKey_inactive[inactiveAddr]: ", common.AddrToKey_inactive[inactiveAddr])
		
		lastIndex := len(common.AddrToKey_inactive[inactiveAddr]) - 1
		ii := 0
		for ii <= lastIndex {
			log.Info("### addrtoKey_inactive", "ii", ii, ".", common.AddrToKey_inactive[inactiveAddr][ii])
			ii++
		}

		inactiveKey := common.AddrToKey_inactive[inactiveAddr][lastIndex]

		log.Info("### restoration target", "address", inactiveAddr)
		log.Info("### restoration target", "key", inactiveKey)

		cnt++

		// blockNum은 restore.py에서 지정한 checkpointBlock의 number를 받는다. 

		// get block number to start restoration
		cnt++
		
		blockNum := big.NewInt(0)
		log.Info("### flag 1")
		blockNum.SetBytes(data[1].([]byte))
		log.Info("### flag 2")
		log.Info("### block num", "blocknum", blockNum.Int64())
		log.Info("### flag 3")
		checkpointBlock := blockNum.Uint64() // TODO: blockNum -> checkpointBlock을 간소화 할 것. (joonha)
		log.Info("### flag 4")
		log.Info("### Checkpoint Block", "checkpointBlock", checkpointBlock)


		/***************************************/
		// PROOVE                
		/***************************************/
		// prove if this account is in the inactive trie.
		var curAcc, resAcc *state.Account
		curAcc = nil
		resAcc = &state.Account{}
		resAcc.Balance = big.NewInt(0)
		var accounts []*state.Account

		cnt++ // TODO: 흩어져 있는 cnt++ 을 합치기 (joonha)

		log.Info("### flag 4-0", "cnt", cnt, "limit", limit)

		for cnt < limit {

			log.Info("### flag 4-0", "cnt", cnt, "limit", limit)
			log.Info("### flag 4-1: cnt < limit")

			/***************************************/
			// GET MERKLE PROOF
			/***************************************/
			// get a merkle proof from tx data
			merkleProof, blockHeader := parseProof(data, int64(checkpointBlock), &cnt, limit)

			log.Info("### flag 4-2")



			/***************************************/
			// VERIFY MERKLE PROOF
			/***************************************/
			// if verification fails, return nil right away (joonha)
			// hint: Has and Get function should be declared in statedb.go
			log.Info("### merkleProof", "merkleProof", merkleProof)
			log.Info("inactiveKey", "inactiveKey", inactiveKey)
			acc, merkleErr := trie.VerifyProof(blockHeader.Root, inactiveKey.Bytes(), &merkleProof)
			log.Info("### flag 4-3")

			if merkleErr != nil {
				log.Info("### flag 4-4")

				// bad merkle proof. something is wrong
				log.Info("Restore Error: bad merkle proof")
				return nil, gas, ErrInvalidProof
			}

			log.Info("### flag 4-5")

			if acc == nil {
				log.Info("### flag 4-6")

				log.Info("No account in the merkle proof")

				// there is no account
				accounts = append(accounts, nil)
			} else {
				log.Info("There is the account in the merkle proof")

				log.Info("### flag 4-7")

				// there is the account
				curAcc = &state.Account{}
				log.Info("### flag 4-8")

				rlp.DecodeBytes(acc, &curAcc)
				log.Info("### flag 4-9")

				accounts = append(accounts, curAcc)
				log.Info("### flag 4-10")

			}
		}

		// Reaching here, it means the proof is valid.

		// get target account at the checkpointBlock
		log.Info("### flag 4-11")

		blockHash := rawdb.ReadCanonicalHash(rawdb.GlobalDB, checkpointBlock)
		blockHeader := rawdb.ReadHeader(rawdb.GlobalDB, blockHash, checkpointBlock)
		
		log.Info("### blockHash", "blockHash", blockHash)
		log.Info("### blockHeader", "blockHeader", blockHeader)

		// hint: Database() should be declared in vm/interface.go
		cachedState, _ := state.New(blockHeader.Root, evm.StateDB.Database(), nil) // snapshot -> nil

		log.Info("### cachedState", "cachedState", cachedState)

		// deal with the checkpointBlock's account state
		log.Info("### account num", "len(accounts)", len(accounts))
		isExist := cachedState.Exist(inactiveAddr)

		// inactive 영역에도 있고 active 영역에도 있으면, GetAccount는 무엇을 받아올까? 
		// 이 부분을 명확히 해 주어야 할 듯.
		// -> statedb.go의 getDeletedStateObject에서 restore의 경우에
		// AddrToKey_inactive로부터 TryGet 하도록 변경하여 해결함.

		if isExist {
			log.Info("### flag 5")
			// there is the account
			curAcc = cachedState.GetAccount(inactiveAddr)
			log.Info("### curACC", "curACC", curAcc)
			accounts = append(accounts, curAcc)
		} else {
			log.Info("### flag 6: NO ACCOUNT is found in the trie")
			// there is no account
			accounts = append(accounts, nil)

			log.Info("Restore Error: no accounts to restore")
			return nil, gas, ErrInvalidProof // TODO: this error msg should be altered. (joonha)
		}

		// Reaching here, 'accounts' contains a list of accounts to be restored
		// in the state trie.

		/***************************************/
		// MERGE INACTIVE HOMOGENEOUS ACCOUNTS    ---> 보류(현재 가장 최근의 key만을 restore하기 때문.)
		/***************************************/
		log.Info("Restore Info before be compact", "checkpointBlock", checkpointBlock, "accounts", accounts)

		// (현재)
		// accounts 리스트에는 하나의 account만이 있다는 가정.
		// 이 account는 addrToKey_inactive의 가장 최근 key 임.
		// addr이 아니라 (incremental) key가 담겨있음에 유의.
		// 
		// 여러 inactive account를 한번에 restore하는 경우에는 이 부분이 수정돼야 함.

		
		/***************************************/
		// RESTORE
		/***************************************/

		log.Info("### account num", "len(accounts)", len(accounts))
		if len(accounts) == 0 {
			// Error: no accounts to restore (no need to restore)
			log.Info("Restore Error: no accounts to restore")
			return nil, gas, ErrInvalidProof
		}

		// CREATE OR MERGE

		// CREATE (no Active account in active trie)
		log.Info("### flag 10")
		if(common.HashToInt64(common.AddrToKey[inactiveAddr]) <= common.InactiveBoundaryKey) {
			log.Info("### flag 11")
			common.Restoring = 0 // ref: statedb.go/getDeletedStateObject function
			evm.StateDB.CreateAccount(inactiveAddr) // create inactive account to state trie
			common.Restoring = 1
			log.Info("### flag 12")
			resAcc.Balance.Add(resAcc.Balance, accounts[1].Balance)
			log.Info("### flag 13")
		} else { // MERGE (Active account in active trie)
			log.Info("### flag 14")
			activeBalance := evm.StateDB.GetBalance(inactiveAddr) // Addr의 GetBalance가 맞고, inactive 것은 제외되고 있음.
			log.Info("### flag 15")
			resAcc.Balance.Add(activeBalance, accounts[1].Balance)
			log.Info("### flag 16")
		}

		// 세 번째 인자로 최종 balance를 넘김.
		log.Info("### flag 17")
		evm.Context.Restore(evm.StateDB, inactiveAddr, resAcc.Balance, evm.Context.BlockNumber) // restore balance
		log.Info("### flag 18")
		

		/***************************************/
		// REMOVE FROM INACTIVE TRIE
		/***************************************/

		// 여기서 삭제를 하면 두 번째 호출 시에 에러가 발생한다.
		// 그래서 우선 comment-out 했다.

		// common.Flag 0: 첫째 시행, 1: 둘째 시행
		if common.Flag == 1 {
			// 리스트에서 삭제 (removing last elem from the slice)
			if len(common.AddrToKey_inactive[inactiveAddr]) > 0 {
				common.AddrToKey_inactive[inactiveAddr] = common.AddrToKey_inactive[inactiveAddr][:len(common.AddrToKey_inactive[inactiveAddr])-1]
			}
			// 만약 그 리스트가 empty면 그 리스트를 지움.
			// _, ok := common.AddrToKey_inactive[inactiveAddr];
			// if !ok { // empty map
			// 	delete(common.AddrToKey_inactive, inactiveAddr);
			// }
			log.Info("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ 1")
			common.Flag = 0
		} else {
			log.Info("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ 0")
			common.Flag = 1
		}
		
		// Remove inactive account from inactive Trie!	
		
		// common.KeysToDelete = make([]common.Hash, 0) // init // added when debugging
		keysToDelete := append(common.KeysToDelete, common.BytesToHash(inactiveKey[:]))
		evm.StateDB.DeletePreviousLeafNodes(keysToDelete)
		common.KeysToDelete = make([]common.Hash, 0) // init

		// restoration ends
		common.Restoring = 0 

	} else { // no restoration (normal transaction)
		// value transfer tx
		evm.Context.Transfer(evm.StateDB, caller.Address(), addr, value)
	}

	// Capture the tracer start/end events in debug mode
	if evm.vmConfig.Debug && evm.depth == 0 {
		evm.vmConfig.Tracer.CaptureStart(evm, caller.Address(), addr, false, input, gas, value)
		defer func(startGas uint64, startTime time.Time) { // Lazy evaluation of the parameters
			evm.vmConfig.Tracer.CaptureEnd(ret, startGas-gas, time.Since(startTime), err)
		}(gas, time.Now())
	}

	if isPrecompile {
		ret, gas, err = RunPrecompiledContract(p, input, gas)
	} else {
		// Initialise a new contract and set the code that is to be used by the EVM.
		// The contract is a scoped environment for this execution context only.
		code := evm.StateDB.GetCode(addr)
		if len(code) == 0 {
			ret, err = nil, nil // gas is unchanged
		} else {
			addrCopy := addr
			// If the account has no code, we can abort here
			// The depth-check is already done, and precompiles handled above
			contract := NewContract(caller, AccountRef(addrCopy), value, gas)
			contract.SetCallCode(&addrCopy, evm.StateDB.GetCodeHash(addrCopy), code)
			ret, err = run(evm, contract, input, false)
			gas = contract.Gas
		}
	}
	// When an error was returned by the EVM or when setting the creation code
	// above we revert to the snapshot and consume any gas remaining. Additionally
	// when we're in homestead this also counts for code storage gas errors.	
	if err != nil {
		evm.StateDB.RevertToSnapshot(snapshot)
		if err != ErrExecutionReverted {
			gas = 0
		}
		// TODO: consider clearing up unused snapshots:
		//} else {
		//	evm.StateDB.DiscardSnapshot(snapshot)
	}
	return ret, gas, err
}

// parseProof get a merkle proof from tx data (joonha)
func parseProof(data []interface{}, blockNum int64, cnt *int, limit int) (state.ProofList, *types.Header) {

	// Get block header
	blockHash := rawdb.ReadCanonicalHash(rawdb.GlobalDB, uint64(blockNum))
	blockHeader := rawdb.ReadHeader(rawdb.GlobalDB, blockHash, uint64(blockNum))

	log.Info("### flag 101")

	// get Merkle proof
	merkleProof := make(state.ProofList, 0)

	log.Info("### flag 102")
	n := big.NewInt(0)
	log.Info("### flag 103")
	n.SetBytes(data[*cnt].([]byte))
	log.Info("### flag 104")

	for *cnt < limit {
		log.Info("### flag 105")
		pf := data[*cnt].([]byte)
		// log.Info("### print proofs", "proofs", pf)
		merkleProof = append(merkleProof, pf)
		*cnt++
	}
	*cnt++ // for iteration

	log.Info("### flag 107")
	return merkleProof, blockHeader
}


// CallCode executes the contract associated with the addr with the given input
// as parameters. It also handles any necessary value transfer required and takes
// the necessary steps to create accounts and reverses the state in case of an
// execution error or failed value transfer.
//
// CallCode differs from Call in the sense that it executes the given address'
// code with the caller as context.
func (evm *EVM) CallCode(caller ContractRef, addr common.Address, input []byte, gas uint64, value *big.Int) (ret []byte, leftOverGas uint64, err error) {
	if evm.vmConfig.NoRecursion && evm.depth > 0 {
		return nil, gas, nil
	}
	// Fail if we're trying to execute above the call depth limit
	if evm.depth > int(params.CallCreateDepth) {
		return nil, gas, ErrDepth
	}
	// Fail if we're trying to transfer more than the available balance
	// Note although it's noop to transfer X ether to caller itself. But
	// if caller doesn't have enough balance, it would be an error to allow
	// over-charging itself. So the check here is necessary.
	if !evm.Context.CanTransfer(evm.StateDB, caller.Address(), value) {
		return nil, gas, ErrInsufficientBalance
	}
	var snapshot = evm.StateDB.Snapshot()

	// It is allowed to call precompiles, even via delegatecall
	if p, isPrecompile := evm.precompile(addr); isPrecompile {
		ret, gas, err = RunPrecompiledContract(p, input, gas)
	} else {
		addrCopy := addr
		// Initialise a new contract and set the code that is to be used by the EVM.
		// The contract is a scoped environment for this execution context only.
		contract := NewContract(caller, AccountRef(caller.Address()), value, gas)
		contract.SetCallCode(&addrCopy, evm.StateDB.GetCodeHash(addrCopy), evm.StateDB.GetCode(addrCopy))
		ret, err = run(evm, contract, input, false)
		gas = contract.Gas
	}
	if err != nil {
		evm.StateDB.RevertToSnapshot(snapshot)
		if err != ErrExecutionReverted {
			gas = 0
		}
	}
	return ret, gas, err
}

// DelegateCall executes the contract associated with the addr with the given input
// as parameters. It reverses the state in case of an execution error.
//
// DelegateCall differs from CallCode in the sense that it executes the given address'
// code with the caller as context and the caller is set to the caller of the caller.
func (evm *EVM) DelegateCall(caller ContractRef, addr common.Address, input []byte, gas uint64) (ret []byte, leftOverGas uint64, err error) {
	if evm.vmConfig.NoRecursion && evm.depth > 0 {
		return nil, gas, nil
	}
	// Fail if we're trying to execute above the call depth limit
	if evm.depth > int(params.CallCreateDepth) {
		return nil, gas, ErrDepth
	}
	var snapshot = evm.StateDB.Snapshot()

	// It is allowed to call precompiles, even via delegatecall
	if p, isPrecompile := evm.precompile(addr); isPrecompile {
		ret, gas, err = RunPrecompiledContract(p, input, gas)
	} else {
		addrCopy := addr
		// Initialise a new contract and make initialise the delegate values
		contract := NewContract(caller, AccountRef(caller.Address()), nil, gas).AsDelegate()
		contract.SetCallCode(&addrCopy, evm.StateDB.GetCodeHash(addrCopy), evm.StateDB.GetCode(addrCopy))
		ret, err = run(evm, contract, input, false)
		gas = contract.Gas
	}
	if err != nil {
		evm.StateDB.RevertToSnapshot(snapshot)
		if err != ErrExecutionReverted {
			gas = 0
		}
	}
	return ret, gas, err
}

// StaticCall executes the contract associated with the addr with the given input
// as parameters while disallowing any modifications to the state during the call.
// Opcodes that attempt to perform such modifications will result in exceptions
// instead of performing the modifications.
func (evm *EVM) StaticCall(caller ContractRef, addr common.Address, input []byte, gas uint64) (ret []byte, leftOverGas uint64, err error) {
	if evm.vmConfig.NoRecursion && evm.depth > 0 {
		return nil, gas, nil
	}
	// Fail if we're trying to execute above the call depth limit
	if evm.depth > int(params.CallCreateDepth) {
		return nil, gas, ErrDepth
	}
	// We take a snapshot here. This is a bit counter-intuitive, and could probably be skipped.
	// However, even a staticcall is considered a 'touch'. On mainnet, static calls were introduced
	// after all empty accounts were deleted, so this is not required. However, if we omit this,
	// then certain tests start failing; stRevertTest/RevertPrecompiledTouchExactOOG.json.
	// We could change this, but for now it's left for legacy reasons
	var snapshot = evm.StateDB.Snapshot()

	// We do an AddBalance of zero here, just in order to trigger a touch.
	// This doesn't matter on Mainnet, where all empties are gone at the time of Byzantium,
	// but is the correct thing to do and matters on other networks, in tests, and potential
	// future scenarios
	evm.StateDB.AddBalance(addr, big0)

	if p, isPrecompile := evm.precompile(addr); isPrecompile {
		ret, gas, err = RunPrecompiledContract(p, input, gas)
	} else {
		// At this point, we use a copy of address. If we don't, the go compiler will
		// leak the 'contract' to the outer scope, and make allocation for 'contract'
		// even if the actual execution ends on RunPrecompiled above.
		addrCopy := addr
		// Initialise a new contract and set the code that is to be used by the EVM.
		// The contract is a scoped environment for this execution context only.
		contract := NewContract(caller, AccountRef(addrCopy), new(big.Int), gas)
		contract.SetCallCode(&addrCopy, evm.StateDB.GetCodeHash(addrCopy), evm.StateDB.GetCode(addrCopy))
		// When an error was returned by the EVM or when setting the creation code
		// above we revert to the snapshot and consume any gas remaining. Additionally
		// when we're in Homestead this also counts for code storage gas errors.
		ret, err = run(evm, contract, input, true)
		gas = contract.Gas
	}
	if err != nil {
		evm.StateDB.RevertToSnapshot(snapshot)
		if err != ErrExecutionReverted {
			gas = 0
		}
	}
	return ret, gas, err
}

type codeAndHash struct {
	code []byte
	hash common.Hash
}

func (c *codeAndHash) Hash() common.Hash {
	if c.hash == (common.Hash{}) {
		c.hash = crypto.Keccak256Hash(c.code)
	}
	return c.hash
}

// create creates a new contract using code as deployment code.
func (evm *EVM) create(caller ContractRef, codeAndHash *codeAndHash, gas uint64, value *big.Int, address common.Address) ([]byte, common.Address, uint64, error) {
	// Depth check execution. Fail if we're trying to execute above the
	// limit.
	if evm.depth > int(params.CallCreateDepth) {
		return nil, common.Address{}, gas, ErrDepth
	}
	if !evm.Context.CanTransfer(evm.StateDB, caller.Address(), value) {
		return nil, common.Address{}, gas, ErrInsufficientBalance
	}
	nonce := evm.StateDB.GetNonce(caller.Address())
	evm.StateDB.SetNonce(caller.Address(), nonce+1)
	// We add this to the access list _before_ taking a snapshot. Even if the creation fails,
	// the access-list change should not be rolled back
	if evm.chainRules.IsBerlin {
		evm.StateDB.AddAddressToAccessList(address)
	}
	// Ensure there's no existing contract already at the designated address
	contractHash := evm.StateDB.GetCodeHash(address)
	if evm.StateDB.GetNonce(address) != 0 || (contractHash != (common.Hash{}) && contractHash != emptyCodeHash) {
		return nil, common.Address{}, 0, ErrContractAddressCollision
	}
	// Create a new account on the state
	snapshot := evm.StateDB.Snapshot()
	evm.StateDB.CreateAccount(address)
	if evm.chainRules.IsEIP158 {
		evm.StateDB.SetNonce(address, 1)
	}
	evm.Context.Transfer(evm.StateDB, caller.Address(), address, value)

	// Initialise a new contract and set the code that is to be used by the EVM.
	// The contract is a scoped environment for this execution context only.
	contract := NewContract(caller, AccountRef(address), value, gas)
	contract.SetCodeOptionalHash(&address, codeAndHash)

	if evm.vmConfig.NoRecursion && evm.depth > 0 {
		return nil, address, gas, nil
	}

	if evm.vmConfig.Debug && evm.depth == 0 {
		evm.vmConfig.Tracer.CaptureStart(evm, caller.Address(), address, true, codeAndHash.code, gas, value)
	}
	start := time.Now()

	ret, err := run(evm, contract, nil, false)

	// Check whether the max code size has been exceeded, assign err if the case.
	if err == nil && evm.chainRules.IsEIP158 && len(ret) > params.MaxCodeSize {
		err = ErrMaxCodeSizeExceeded
	}

	// if the contract creation ran successfully and no errors were returned
	// calculate the gas required to store the code. If the code could not
	// be stored due to not enough gas set an error and let it be handled
	// by the error checking condition below.
	if err == nil {
		createDataGas := uint64(len(ret)) * params.CreateDataGas
		if contract.UseGas(createDataGas) {
			evm.StateDB.SetCode(address, ret)
		} else {
			err = ErrCodeStoreOutOfGas
		}
	}

	// When an error was returned by the EVM or when setting the creation code
	// above we revert to the snapshot and consume any gas remaining. Additionally
	// when we're in homestead this also counts for code storage gas errors.
	if err != nil && (evm.chainRules.IsHomestead || err != ErrCodeStoreOutOfGas) {
		evm.StateDB.RevertToSnapshot(snapshot)
		if err != ErrExecutionReverted {
			contract.UseGas(contract.Gas)
		}
	}

	if evm.vmConfig.Debug && evm.depth == 0 {
		evm.vmConfig.Tracer.CaptureEnd(ret, gas-contract.Gas, time.Since(start), err)
	}
	return ret, address, contract.Gas, err
}

// Create creates a new contract using code as deployment code.
func (evm *EVM) Create(caller ContractRef, code []byte, gas uint64, value *big.Int) (ret []byte, contractAddr common.Address, leftOverGas uint64, err error) {
	contractAddr = crypto.CreateAddress(caller.Address(), evm.StateDB.GetNonce(caller.Address()))
	return evm.create(caller, &codeAndHash{code: code}, gas, value, contractAddr)
}

// Create2 creates a new contract using code as deployment code.
//
// The different between Create2 with Create is Create2 uses sha3(0xff ++ msg.sender ++ salt ++ sha3(init_code))[12:]
// instead of the usual sender-and-nonce-hash as the address where the contract is initialized at.
func (evm *EVM) Create2(caller ContractRef, code []byte, gas uint64, endowment *big.Int, salt *uint256.Int) (ret []byte, contractAddr common.Address, leftOverGas uint64, err error) {
	codeAndHash := &codeAndHash{code: code}
	contractAddr = crypto.CreateAddress2(caller.Address(), salt.Bytes32(), codeAndHash.Hash().Bytes())
	return evm.create(caller, codeAndHash, gas, endowment, contractAddr)
}

// ChainConfig returns the environment's chain configuration
func (evm *EVM) ChainConfig() *params.ChainConfig { return evm.chainConfig }
