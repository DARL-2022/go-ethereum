package trie

import (
	"errors"
	"fmt"
	"os"
	"sort"
	"strconv"
	"sync"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

var path = "/home/jhkim/go/src/github.com/ethereum/go-ethereum/txDetail/"
var _ = os.MkdirAll(path, 0777)

func increaseSize(nodeSize int, node string, tir *TrieInspectResult, depth int) {
	rwMutex.Lock()
	tir.TrieSize += nodeSize
	if node == "short" {
		tir.ShortNodeNum++
		tir.ShortNodeSize += nodeSize
		tir.StateTrieShortNodeDepth[depth]++

	} else if node == "full" {
		tir.FullNodeNum++
		tir.FullNodeSize += nodeSize
		tir.StateTrieFullNodeDepth[depth]++

	} else if node == "value" {
		tir.LeafNodeNum++
		tir.LeafNodeSize += nodeSize
		tir.StateTrieLeafNodeDepth[depth]++
	} else {
		fmt.Println("wrong node format in increaseSize")
		os.Exit(1)
	}
	rwMutex.Unlock()
}

// check whether slice contains key (jhkim)
func contain(key common.Hash, slice []common.Hash) bool {
	for _, a := range slice {
		if a == key {
			return true
		}
	}
	return false
}

type TxInformation struct {
	BlockNumber int64
	From        common.Address
	To          common.Address
	FromAdrHash common.Hash
	ToAdrHash   common.Hash
	Types       int // 1: send, 2: contract creation, 3: contract call, 0: etc.
	Else        []common.Address

	ContractAddress_SlotHash map[common.Address][]common.Hash
	SlotHash                 []common.Hash
}

func PrintFlushedNode(blocknumber int) {

	s := "FlushednodeList in each block\n"
	tmp := ""
	for key, val := range common.Flushednode_block {
		s += fmt.Sprintf("{\n  Block %d:", key)
		cf, cn := 0, 0 // count
		tmp = ""
		for k, v := range val {
			tmp += fmt.Sprintf("\t%v", k)
			if v == 1 {
				tmp += fmt.Sprintf("\t Full Node\n")
				cf += 1
			} else {
				tmp += fmt.Sprintf("\t Short Node\n")
				cn += 1
			}

		}
		s += fmt.Sprintf("\t[Full: %d, Short: %d]\n", cf, cn)
		s += fmt.Sprintf(tmp)
		s += fmt.Sprintf("}\n")
	}

	f1, err := os.Create(path + "FlushedNode_" + strconv.FormatInt(int64(blocknumber)-10000, 10) + "-" + strconv.FormatInt(int64(blocknumber), 10) + ".txt") // goroutine version
	if err != nil {
		fmt.Printf("Cannot create result file.\n")
		os.Exit(1)
	}
	defer f1.Close()
	fmt.Fprintln(f1, s) // write text file

	common.Flushednode_block = map[int]map[common.Hash]int{}
}

func PrintAddrhash2Addr(blocknumber int) {
	s := ""
	s += fmt.Sprintln("AddressHash to Addr Map")

	common.AddrHash2AddrSyncMap.Range(func(key, value interface{}) bool {
		k := key.(common.Hash)
		v := value.(common.Address)
		s += fmt.Sprintf("%v,%v\n", k, v)

		return true
	})

	s += fmt.Sprintln()

	f2, err := os.Create(path + "AddrHash2Addr_" + strconv.FormatInt(int64(blocknumber)-10000, 10) + "-" + strconv.FormatInt(int64(blocknumber), 10) + ".txt") // goroutine version
	if err != nil {
		fmt.Printf("Cannot create result file.\n")
		os.Exit(1)
	}
	defer f2.Close()
	fmt.Fprintln(f2, s) // write text file
	common.AddrHash2AddrSyncMap = sync.Map{}
}

func PrintTxDetail(blocknumber int) {
	s := ""
	s += fmt.Sprintln("PrintTxDetail in block", blocknumber)
	common.TxDetailSyncMap.Range(func(key, value interface{}) bool {
		k := key.(common.Hash)
		v := value.(*TxInformation)

		if v.Types != 1 {

			s += fmt.Sprintln("TxID: ", k)
			s += fmt.Sprintln("  Block: ", v.BlockNumber)
			if v.Types == 1 {
				s += fmt.Sprintln("  TxInformation: Transfer")
				// s += fmt.Sprintln("  TxInformation: Transfer or Contract call")
			} else if v.Types == 2 {
				s += fmt.Sprintln("  TxInformation: Contract creation tx")
			} else if v.Types == 3 {
				s += fmt.Sprintln("  TxInformation: Contract call")
			} else {
				s += fmt.Sprintln("  Wrong Tx Information")
			}

			s += fmt.Sprintln("    From: \t\t", v.From)
			if v.Types == 1 {
				s += fmt.Sprintln("    To(EOA): \t\t", v.To)
				// s += fmt.Sprintln("    To: \t\t", v.To)
			} else if v.Types == 3 {
				s += fmt.Sprintln("    To(CA): \t\t", v.To)
			}

			if v.Types != 1 {
				s += fmt.Sprintln("    Contract related Address")
				for _, v := range v.Else {
					s += fmt.Sprintln("      EOA: ", v) // transition reward of miner and EOAs called by contract
				}
				for kk, vv := range v.ContractAddress_SlotHash {

					s += fmt.Sprintln("      Contract Address: ", kk)
					s += fmt.Sprintln("        SlotHash: ", vv)
				}
			}
			s += fmt.Sprintln()
		}

		return true
	})

	f1, err := os.Create(path + "TxDetail_" + strconv.FormatInt(int64(blocknumber)-10000, 10) + "-" + strconv.FormatInt(int64(blocknumber), 10) + ".txt") // goroutine version
	if err != nil {
		fmt.Println("Cannot create result file.", err)
		os.Exit(1)
	}
	defer f1.Close()
	fmt.Fprintln(f1, s) // write text file

	common.TxDetailSyncMap = sync.Map{}

	s = ""
	common.TrieUpdateElse.Range(func(key, value interface{}) bool {
		k := key.(int)
		v := value.([]common.Address)

		// s += fmt.Sprintln("{")
		// s += fmt.Sprintln("  Block", k)
		s += fmt.Sprintf("%v,", k)
		for _, val := range v {
			s += fmt.Sprintf("%v,", val)
		}
		s += fmt.Sprintln("")

		return true

	})

	f2, err := os.Create(path + "TrieUpdateElse_" + strconv.FormatInt(int64(blocknumber)-10000, 10) + "-" + strconv.FormatInt(int64(blocknumber), 10) + ".txt") // goroutine version
	if err != nil {
		fmt.Printf("Cannot create result file.\n")
		os.Exit(1)
	}
	defer f2.Close()
	fmt.Fprintln(f2, s) // write text file

	common.TrieUpdateElse = sync.Map{}

}

func MakeDuplicatedFlushedNode(blocknumber int) {
	s := ""
	s += fmt.Sprintln()

	// pretty print for flushed duplicate node
	for k, v := range common.FlushedNodeDuplicate_block {
		s += fmt.Sprintln(k, len(v), v)
	}
	s += fmt.Sprintln()

	path := path + "DuplicateFlushedNode_" + strconv.FormatInt(int64(blocknumber)-10000, 10) + "-" + strconv.FormatInt(int64(blocknumber), 10) + ".txt"
	if _, err := os.Stat(path); err == nil {
		// path/to/whatever exists
		f1, _ := os.Open(path)
		defer f1.Close()
		fmt.Fprintln(f1, s) // write text file

	} else if errors.Is(err, os.ErrNotExist) {
		// path/to/whatever does *not* exist
		f1, err := os.Create(path)
		defer f1.Close()
		if err != nil {
			fmt.Printf("Cannot create result file.\n")
			os.Exit(1)
		}

		fmt.Fprintln(f1, s) // write text file
	} else {
		fmt.Println("Make Duplicated Flushed Node: File error")
		os.Exit(1)
	}
	common.FlushedNodeDuplicate_block = map[common.Hash][]int{}
	common.FlushedNodeDuplicate = map[common.Hash]int{}
}

// deprecated functions

// choose top N big Storage Trie and return map (jhkim)
func findTopNStorageTrie(StorageTrieNodeMap map[string]([7]int), top_number int) map[string]int {
	topN_map := map[string]int{}
	min_size := 0
	min_codehash := ""
	// min_codehash := "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

	for codehash, value := range StorageTrieNodeMap {
		sizeSum := value[1] + value[3] + value[5] // fullnodesize + shortnodesize + leafnodesize

		if codehash == "" {
			fmt.Println("nil codehash in StorageTrieNodeMap! 1. empty storage Trie 2. Error")
			break

		} else if len(topN_map) < top_number {
			topN_map[codehash] = sizeSum

			if min_size == 0 || sizeSum < min_size {
				min_size = sizeSum
				min_codehash = codehash
			}

		} else if sizeSum <= min_size {
			continue

		} else { // change topN_map
			delete(topN_map, min_codehash)
			min_size = sizeSum
			min_codehash = codehash

			for key, value := range topN_map {
				if value < min_size {
					min_size = value
					min_codehash = key
				}
			}
			topN_map[codehash] = sizeSum
		}
	}

	return topN_map
}

// waitTimeout waits for the waitgroup for the specified max timeout. (jhkim)
// Returns true if waiting timed out.
func waitTimeout(wg *sync.WaitGroup, timeout time.Duration) bool {
	c := make(chan struct{})
	go func() {
		defer close(c)
		wg.Wait()
	}()
	select {
	case <-c:
		return false // completed normally
	case <-time.After(timeout):
		return true // timed out
	}
}

// Descending sort map by value (jhkim)
func sortByValue(m map[string]int) []KV {
	var ss []KV
	for k, v := range m {
		ss = append(ss, KV{k, v})
	}

	sort.Slice(ss, func(i, j int) bool {
		return ss[i].Value > ss[j].Value
	})

	return ss
}
