
# remove exists txDetail dir
cd ../..
# rm -rvf txDetail/*
make geth

# WARNING: delete geth datadir. 
DataDir="/ethereum/geth" # procyon
# DataDir="/ssd/ethereum" # lynx
# echo "clear chaindata"
# rm -rf ${DataDir} && mkdir ${DataDir}

cd build/bin
if [ -n "$1" ]; then # if arguements exists
	echo 'epoch of txdetail:' $1
	./geth --datadir ${DataDir} --syncmode=full --gcmode=archive --http --http.port "8082" --port 30304 --http.corsdomain="*" --http.api="admin,eth,debug,miner,net,txpool,personal,web3" --snapshot=false --txdetail $1 
else
	echo 'default epoch of txdetail: 100000'
	./geth --datadir ${DataDir} --syncmode=full --gcmode=archive --http --http.port "8082" --port 30304 --http.corsdomain="*" --http.api="admin,eth,debug,miner,net,txpool,personal,web3" --snapshot=false --txdetail 100000
fi





