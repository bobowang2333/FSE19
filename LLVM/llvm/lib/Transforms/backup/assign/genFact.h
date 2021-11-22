#pragma once
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include <stdint.h>

using namespace llvm;
namespace assign {
    class genFact : public InstVisitor<genFact> {
        private:
            raw_fd_ostream *datalogFiles;
            std::map<Instruction*, int> IDMap;
            std::vector<std::string> RAND_VAR;
            std::vector<std::string> CONSTANT_VAR;
            std::vector<std::string> KEY_VAR;
            unsigned input_s;
            unsigned input_bitset;
            /** ths format is used for the SMT-LIB2 **/
            bool useIntIDs;
            /** add specification to the passed ostream **/
            void addDatalogSpec(raw_fd_ostream &f);
            /** return the comment char **/
            char getCommentMark();
            /** convert a int to the bit-vec style string **/
            std::string ToBitVecForm(unsigned, unsigned);
            /** return a string representing the assignment **/
            //std::string createAssign(Value *to, Value *from);
            std::string createAssign(std::string to, std::string from);
            std::string createLoadAssign(std::string to, std::string from);
            /** return a string representing the xor assignment **/
            std::string createXor(std::string to, std::string from, std::string OP_ID);
            /** return a string representing the and/or assignment **/
            std::string createAndOr(std::string to, std::string from, std::string OP_ID);
            /** return a string representing the load **/
            std::string createLoad(Value *to, Value *from);
            /** return a string representing the store fact **/
            std::string createStore(Value *from1, Value *from2);
            std::string createStoreAssign(std::string to, std::string from);
            /** return a string representing the binary operation **/
            std::string createBinaryOp(Value *to, Value *from, std::string OP_ID);
            /** write the passed datalog with the passed value **/
            void writeFact(Value *v, std::string fact);

        public:
            genFact(raw_fd_ostream *os, std::map<Instruction*, int>, std::vector<std::string>, std::vector<std::string>, std::vector<std::string>, unsigned, unsigned);
            //override the visitor function
            //void visitReturnInst(ReturnInst &I);
            //void visitCallInst(CallInst &I);
            //void visitInvokeInst(InvokeInst &I);
            void visitLoadInst(LoadInst &I);
            void visitBinaryOperator(BinaryOperator &I);
            void visitStoreInst(StoreInst &I);
            //void visitAllocaInst(AllocaInst &I);
    };
}
