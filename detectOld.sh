#!/bin/sh
#########this is the beginning of the execution of the shell script############
clang -emit-llvm -S ssa.cpp -o ssa.ll

#echo ******** from backend generating the shared register information == memOperand.log ******
/Users/bobobo/Documents/llvm-3.6/xcode_build_v2/Debug/bin/llc -regalloc=basic -debug-only=regalloc ssa.ll -o ssa.s &> /dev/null
#cp ~/Documents/llvm-3.6/xcode_build_v2/Debug/bin/memBool.log .

/Users/bobobo/Documents/benchmark/hw_benchmark/binary/analy_backend memBool.log share_variable.txt

#echo **********************generate the input file input.txt********************
#/Users/bobobo/Documents/benchmark/hw_benchmark/binary/rw_input

#echo ************************LLVM pass generate the Z3 file***************************
opt -load /Users/bobobo/Documents/llvm-3.6/xcode_build_v2/Debug/lib/LLVMfactInt.dylib -factInt -input input.txt -share share_variable.txt ssa.ll

#echo ********utilize z3 to calculate the fixed point***********
z3 -smt2 compute.smt2 &> res.txt

#echo **********************map the ID and TYPE to the intermediate variables********************************
../common/extract_res compute.smt2 res.txt output.txt

#echo **********************generate the interface of HD sensitive variable to LLVM backend for mitigation*******************
../common/interfaceBackend output.txt memOriginal.log forBackend.txt

