/***** print code for later datalog output *****/
/***** author: Jingbo Wang ********************/

#define DEBUG_TYPE "printCode_bobo"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <vector>
#include <map>

using namespace llvm;
namespace {
    class printCode : public FunctionPass {
        public:
            static char ID;
            printCode(): FunctionPass(ID) {}
            /** runOnFunction **/
            virtual bool runOnFunction(Function &F)
            {
                /** print function name **/
                std::cerr << "Function " << F.getName().str() << "\n";
                //static int bb_number = 1;
                int bb_number = 1;
                //static int inst_number = 1;
                int inst_number = 1;
                std::map<BasicBlock*, int> bb_map;
                std::map<Instruction*, int> inst_map;
                Function::iterator f_it;
                BasicBlock::iterator bb_it;

                /** assign numbers to each BasicBlock and Instruction **/
                for(f_it = F.begin(); f_it != F.end(); f_it++)
                {
                    BasicBlock *bb = &*f_it;
                    bb_map.insert(std::pair<BasicBlock*, int>(bb, bb_number));
                    bb_number++;
                    for(bb_it = bb->begin(); bb_it != bb->end(); bb_it++)
                    {
                        Instruction *inst = &*bb_it;
                        inst_map.insert(std::pair<Instruction*, int>(inst, inst_number));
                        inst_number++;
                    }
                }

                /** print BB/Inst  with its number **/
                for(f_it = F.begin(); f_it != F.end(); f_it++)
                {
                    BasicBlock *bb = &*f_it;
                    //std::cerr << "\n" << "BasicBlock " << bb_map[bb] << "\n";
                    errs() << "\n" << (bb->getName()) << "\n";
                    for(bb_it = bb->begin(); bb_it != bb->end(); bb_it++)
                    {
                        Instruction *inst = &*bb_it;
                        int num = inst_map[inst];
                        const char *opcode_name = inst->getOpcodeName();
                        std::cerr << "%" << num << ":" << opcode_name;

                        /** print the operands **/
                        User::op_iterator op_it;
                        for(op_it = inst->op_begin(); op_it != inst->op_end(); op_it++)
                        {
                            Use *u = &*op_it;
                            Value *v = u->get();
                            if(isa<Instruction>(u))
                                std::cerr << " %" << inst_map[(Instruction*) v];
                            else if(v->hasName())
                                std::cerr << " %" << v->getName().str();
                            else
                                std::cerr << " XXX";
                        }
                        std::cerr << "\n";
                    }
                }
                std::cerr << "\n";
                return false;
            }

            /** print for later use **/
            virtual void print(std::ostream &O, const Module *M) const {
                O << "This is the PrintCode procedure.\n";
            }

            /** preserve all analysis **/
            virtual void getAnalysisUsage(AnalysisUsage &AU) const {
                AU.setPreservesAll();
            };
    };
    char printCode::ID = 0;
    /** register the printCode Pass **/
    RegisterPass<printCode> X("printCode", "print code", true, false);
}
