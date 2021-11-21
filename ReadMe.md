#README

Here is the artifact for _Mitigating Power Side Channels during Compilation_, which is implemented in LLVM 3.6 and we also used the \muZ Datalog engine in Z3 to infer types. Before running our tool, make sure that Z3 is correctly installed. 

Since our method modifies the source code of LLVM, this artifact contains the new source code of LLVM 3.6. You just need to install LLVM on your device with our source code.

##Installation
### Cmake
First, download our source code for LLVM 3.6.
Second, install [cmake](https://cmake.org/download/). If you type cmake in the terminal and obtain
```
-bash: cmake: command not found
```
. Then export the cmake path to PATH globally.

```
export PATH=/Applications/CMake.app/Contents/bin:$PATH
```

### LLVM
- Select a directory to install LLVM. ``` $ YourPathToFSE19/FSE19/LLVM```
- You need to install clang corresponding to LLVM 3.6 version. You can also install additional clang tools in 
```
llvm/tools/clang/tools
```
.

- Then you can start to compile LLVM and Clang. 

	```
	$ cd YourPathToFSE19/FSE19/LLVM
	$ mkdir build
	$ cd build 
	$ cmake -G "Unix Makefiles" ../llvm
	$ make
	$ export PATH=YourPathToFSE19/FSE19/LLVM/build/bin:$PATH
	```

### Z3
For brevity, you can just refer to [Z3](https://github.com/Z3Prover/z3) for installing Z3 theorem prover.

## Running Instruction
Here we document all the running instructions, which are divided into two parts. First, we introduce how to run the type inference to detect the HD sensitive variables. Second, we introduce how to run the backend for generating a leak-free assembly.

### FrontEnd: Type Inference

- You rename the source cpp file in your benchmark to **ssa.cpp**, ensuring that the code complies with the SSA format. 
- Run the **detect.sh** to detect the HD-sensitive pairs from the input source code. For instance, we run the benchmark P3 in <em>FSE19</em> directory.

```
$ cd YourPathToFSE19/FSE19/P3
$ ../detect.sh ssa.cpp
```

After running the above instructions, we will document the leaky variables in the generated file <em>forBackend.txt</em>.

Later, we describle how the **detect.sh** file detects the sensitive variables.

1. In the <em>detect.sh</em> file, we firstly generate the IR file **ssa.ll** from source code **ssa.cpp**.

  ```
clang -emit-llvm -S ssa.cpp -o ssa.ll
  ``` 
2. The shared register information **memOperand.log** is generated from running the backend. 
	```
	YourPathToFSE19/FSE19/LLVM/build/Debug/bin/llc -regalloc=basic -debug-only=regalloc ssa.ll -o ssa.s &> /dev/null
	```
3. Analyze the backend results to produce the shared register information.
	```
	YourPathToFSE19/FSE19/common/analy_backend memBool.log share_variable.txt
	```
4. Apply LLVM pass to generate the Z3 file.
	```
	opt -load YourPathToFSE19/FSE19/LLVM/build/Debug/lib/LLVMfactInt.dylib -factInt -input input.txt -share share_variable.txt ssa.ll
	```
	Here, <em>LLVMfactInt.dylib</em> is the name of LLVM pass I have built. The source code is in the follwing directory. 
	 
	```
	YourPathToFSE19/FSE19/LLVM/llvm/lib/Transforms/factInt
	```
	The building process of this LLVM pass is emitted here.
5. Apply z3 to calculate the fixed point
	```
	z3 -smt2 compute.smt2 &> res.txt
	```
6. We then process the results **res.txt**, for mapping the ID and TYPE to the intermediate variables.
	```
	../common/extract_res compute.smt2 res.txt output.txt
	```
7. We then generate the interface of HD sensitive variable to LLVM backend for mitigation.
	```
	../common/interfaceBackend output.txt memOriginal.log forBackend.txt
	```

### Backend: Produce Leak-Free Assembly

- After obtaining the leaky variables in file <em>forBackend.txt</em>, our modified backend (**llc**) will take it as input to rewrite the register allocation part. For instance, the running instruction in my laptop
```
$ /Users/bobobo/Documents/llvm-3.6/xcode_build_v2/Debug/bin/llc -regalloc=basic  -debug-only=isel YourPathToFSE19/FSE19/P3/ssa.ll -o ssa_new.s
```

The newly generated assembly file <em>ssa_new.s</em> is a leak-free assembly.
## Notes
- We also provide the SSA preprocessing scripts for our benchmarks. If you want to extend to your benchmark, you may have to modify the preprocessing scripts.
- Also, our analysis is intra-procedural and you may have to inline all the functions.





