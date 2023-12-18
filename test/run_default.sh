#!/bin/sh

dirs=("two_phase/all_msgs_env/two_phase_9"
    "two_phase/all_msgs_env/two_phase_10"
    "two_phase/counter"
    "endive_benchmarks/client_server_ae/client_server_ae_422"
    "endive_benchmarks/client_server_ae/client_server_ae_242"
    "endive_benchmarks/client_server_db_ae/client_server_db_ae_422"
    "endive_benchmarks/client_server_db_ae/client_server_db_ae_232"
    "endive_benchmarks/consensus_forall"
    "endive_benchmarks/firewall"
    "endive_benchmarks/learning_switch"
    "endive_benchmarks/lockserv/lockserv_15"
    "endive_benchmarks/lockserv/lockserv_16"
    "endive_benchmarks/paxos")

for d in ${dirs[*]}
do
    pushd "$d"
    ./default.sh
    popd
    echo "\n"
done
