
cd ../..
make geth
cd build/bin


# DataDir="/ssd/ethereum" # lynx
DataDir="/ethereum/geth" # procyon




./geth --datadir ${DataDir} db trieinspect $1

