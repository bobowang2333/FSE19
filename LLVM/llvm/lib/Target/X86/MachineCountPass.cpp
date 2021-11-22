//
//  MachineCountPass.cpp
//  
//
//  Created by bobobo on 3/29/18.
//
//

#include "X86.h"
#include "llvm/pass.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "machinecount"

using namespace llvm;

namespace  {
    class MachineCountPass : public MachineFunctionPass {
    public:
        static char ID;
        MachineCountPass() : MachineFunctionPass(ID) {}
        virtual bool runOnMachineFunction(MachineFunction &MF){
            
            unsigned num_instr = 0;
            for(auto &MBB : MF){
                for(MachineBasicBlock::const_iterator BBI = MBB.begin(), BBE = MBB.end(); BBI != BBE; ++BBI)
                    ++num_instr;
            }
            outs() << ">>>" << MF.getName() << " has " << num_instr << " instructions!\n";
            return false;
        }
    };
}

namespace llvm {
    FunctionPass *createMyCustomMachinePass(){
        return new MachineCountPass();
    }
}

char MachineCountPass::ID = 0;
static RegisterPass<MachineCountPass> X("machinecount", "machine count pass");
