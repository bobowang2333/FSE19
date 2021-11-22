/***** add always inline for the function ****/
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Statistic.h"
#include "string"
using namespace llvm;
namespace {
    class addInline : public FunctionPass{
        public:
            static char ID;
            addInline(): FunctionPass(ID) {}
            virtual bool runOnFunction(Function &F)
            {
                std::string f_name = F.getName().str();
                if((f_name.compare("main")) && (f_name.compare("printf")))
                {
                    F.addFnAttr(Attribute::AlwaysInline);
                    //F.addAttribute(0, Attribute::AlwaysInline);
                    return true;
                }else
                {
                    return false;
                }
            }
            virtual void getAnalysisUsage(AnalysisUsage &AU) const{
                AU.setPreservesAll();
            }
    };
    char addInline::ID = 0;
    /** register the addInline pass **/
    RegisterPass<addInline> X("addInline", "add the always_inline attribute", true, false);
}
