package common

// (jhkim)

import (
	"sync"
)

var (
	GlobalTxHash      Hash    = HexToHash("0x0")
	GlobalTxTo        Address = HexToAddress("0x0")
	GlobalTxFrom      Address = HexToAddress("0x0")
	GlobalBlockNumber int     = 0
	// GlobalContractAddress Address = HexToAddress("0x0")

	Flushednode_block = map[int](map[Hash]int){} // key : block number, value: list of node hash
	FlushedNodeList   = map[Hash]int{}           // key : block number, value: list of node hash

	FlushedNodeDuplicate_block = map[Hash][]int{} // key : block number, value: map [key: duplicated node hash, value: count]
	FlushedNodeDuplicate       = map[Hash]int{}   // 1: already existed

	// AddrHash2Addr              = map[Hash]Address{}       // key : AddressHash, value: Ethereum Address
	AddrHash2AddrSyncMap = sync.Map{} // key : AddressHash, value: Ethereum Address
	// TxDetail                   = map[Hash]*TxInformation{} // key : TxID, value: struct TxInformation
	TxDetailSyncMap    = sync.Map{}
	TrieUpdateElse     = sync.Map{} // include miner and else // key: blocknumber, value: list of Address
	TrieUpdateElseTemp = []Address{}

	Coinbase Address = HexToAddress("0xc4422d1C18E9Ead8A9bB98Eb0d8bB9dbdf2811D7")
	// TxDetailHashmap = map[string]([]Hash){}    // key : TxID(temporaliy set string), value: addressHash List{from , to, isCA(boolean)}
	// CASlotHash      = map[Hash][]Hash{}        // key : CA addressHash
)
