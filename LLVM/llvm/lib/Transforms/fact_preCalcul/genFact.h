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
            // precompute rec_all_inc and rec_rand_var
            std::map<Instruction*, std::vector<unsigned>> REC_ALL_INC;
            std::map<Instruction*, std::vector<unsigned>> REC_RAND_VAR;
            unsigned input_s;
            unsigned input_ind;
            unsigned input_num;
            unsigned input_bitset;
            /** ths format is used for the SMT-LIB2 **/
            bool useIntIDs;
            /** add specification to the passed ostream **/
            void addDatalogSpec(raw_fd_ostream &f);
            /** return the comment char **/
            char getCommentMark();
            /** convert a int to the bit-vec style string **/
            std::string ToBitVecForm(unsigned input, unsigned max_len);
            std::string ToBitVecForm_original (unsigned input, unsigned max_len);
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
            /** return a string representing the binary operation with a constant **/
            std::string createBinaryConstant(Value *to, Value *from);
            /** return a string representing the zext and trunc relation **/
            std::string createTrunc(Value *to, Value *from);
            std::string createICmpInst(Value *to, Value *from);
            /** return the relation inside a alloca instr **/
            std::string createAllocaInst(Value *to, std::string alloca_name);
            std::string createZExtInst(Value *to, Value *from);
            /** write the passed datalog with the passed value **/
            void writeFact(Value *v, std::string fact);
            /** write all the REC_RAND_VAR and REC_ALL_INC information **/
            std::string write(Instruction *inst, std::vector<unsigned> rand_var, unsigned type);
            std::string writeZero(Instruction *inst, unsigned type);
            /** precalculate all the rec information before type inference **/
            std::string preCal_load(Value *to, Value *from);
            std::string preCal_binary(Value *to, Value *from1, Value *from2);
            /** the set operations **/
            std::vector<unsigned> SetOr(std::vector<unsigned> a, std::vector<unsigned> b);
            std::vector<unsigned> XOR_ALL_INC(std::vector<unsigned> all_1, std::vector<unsigned> all_2, std::vector<unsigned> rand_1, std::vector<unsigned> rand_2);
            std::vector<unsigned> XOR_RAND_VAR(std::vector<unsigned> rand_1, std::vector<unsigned> rand_2);
        

        public:
            genFact(raw_fd_ostream *os, std::map<Instruction*, int> &IDMap, std::vector<std::string>, std::vector<std::string>, std::vector<std::string>, unsigned, unsigned, unsigned, unsigned, std::map<Instruction*, std::vector<unsigned>>, std::map<Instruction*, std::vector<unsigned>>);
            //override the visitor function
            //void visitReturnInst(ReturnInst &I);
            //void visitCallInst(CallInst &I);
            //void visitInvokeInst(InvokeInst &I);
            void visitLoadInst(LoadInst &I);
            void visitBinaryOperator(BinaryOperator &I);
            void visitStoreInst(StoreInst &I);
            /** for bool value **/
            void visitTruncInst(TruncInst &I);
            void visitICmpInst(ICmpInst &I);
            void visitAllocaInst(AllocaInst &I);
            void visitZExtInst (ZExtInst &I);
    };
}
