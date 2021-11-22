#pragma once
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include <stdint.h>
#include <set>

using namespace llvm;
typedef std::tuple<std::string, std::string> equal_pair;
typedef std::tuple<std::string, std::string, std::string> xor_pair;
namespace assign {
    class genFact : public InstVisitor<genFact> {
        private:
            raw_fd_ostream *datalogFiles;
            raw_fd_ostream *keyFile;
            std::map<Instruction*, int> IDMap;
            std::vector<std::string> RAND_VAR;
            std::vector<std::string> CONSTANT_VAR;
            std::vector<std::string> KEY_VAR;
            // precompute rec_all_inc and rec_rand_var
            std::map<Instruction*, std::vector<unsigned>> REC_ALL_INC;
            std::map<Instruction*, std::vector<unsigned>> REC_RAND_VAR;
            std::map<unsigned, bool> RAND_var;
            std::map<unsigned, bool> KEY_SENSITIVE_var;
            std::map<unsigned, bool> KEY_IND_var;
            //Function F;
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
            std::string createSExtInst(Value *to, Value *from);
            /** write the passed datalog with the passed value **/
            void writeFact(Value *v, std::string fact);
            /** write all the REC_RAND_VAR and REC_ALL_INC information **/
            std::string write(Instruction *inst, std::vector<unsigned> &rand_var, unsigned type);
            std::string writeZero(Instruction *inst, unsigned type);
            /** precalculate all the rec information before type inference **/
            std::string preCal_load(Value *to, Value *from);
            std::string preCal_binary(Value *to, Value *from1, Value *from2);
            /** the set operations **/
            std::vector<unsigned> SetOr(std::vector<unsigned> &a, std::vector<unsigned> &b);
            std::vector<unsigned> XOR_ALL_INC(std::vector<unsigned> &all_1, std::vector<unsigned> &all_2, std::vector<unsigned> &rand_1, std::vector<unsigned> &rand_2);
            std::vector<unsigned> XOR_RAND_VAR(std::vector<unsigned> &rand_1, std::vector<unsigned> &rand_2);
            /** type inference related operation **/
            std::string assign_type(Value *to, Value *from);
            std::string binary_type(Value *to, Value *from1, Value *from2);
            bool BV_DIFF_REC(Instruction *from1, Instruction *from2);
            bool BV_SAME_REC(Instruction *from1, Instruction *from2);
            bool BV_ALL_INTERSECT(Instruction *from1, Instruction *from2);
            unsigned calRange(unsigned j, std::vector<unsigned> &type_var);
            void writeType(std::string fact);
            void writeKey(std::string key);
            std::vector<std::string> hasPrefix(std::vector<equal_pair> &vec_equal, std::string toFind);
            void calEqualSet(Function &F, std::map<std::string, std::string> &new_equal_assign, std::map<std::string, bool> &all_node);
            void equal_dfs( Function &F, unsigned toFind, std::map<unsigned, bool> &marked);
            void adjacent_node(Function &F, std::vector<unsigned> &adjacent, unsigned node);
            void dfs(Function &F, std::string node, std::map<std::string, bool> &marked, std::map<std::string, int> &id, unsigned count, std::vector<std::string> &now_marked);
            void findEqual( Function &F, unsigned toFind, std::vector<unsigned> &res);
        
        public:
            //genFact(raw_fd_ostream *os, std::map<Instruction*, int> &IDMap, std::vector<std::string>, std::vector<std::string>, std::vector<std::string>, unsigned, unsigned, unsigned, unsigned, std::map<Instruction*, std::vector<unsigned>>, std::map<Instruction*, std::vector<unsigned>>, std::vector<unsigned> &RAND_var, std::vector<unsigned>, std::vector<unsigned>);
        genFact(raw_fd_ostream *os, raw_fd_ostream *keyFile, std::map<Instruction*, int> &IDMap, std::vector<std::string> &RAND_VAR, std::vector<std::string> &CONSTANT_VAR, std::vector<std::string> &KEY_VAR, unsigned input_s, unsigned input_ind, unsigned input_num,unsigned input_bitset, std::map<Instruction*, std::vector<unsigned>> &REC_ALL_INC, std::map<Instruction*, std::vector<unsigned>> &REC_RAND_VAR, std::map<unsigned, bool> &RAND_var, std::map<unsigned, bool> &KEY_SENSITIVE_var, std::map<unsigned, bool> &KEY_IND_var);
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
            void visitSExtInst (SExtInst &I);
        void cal_EqualAssign(Function &F, std::map<std::string, std::string> &new_equal_assign);
            void cal_XorAssign(Function &F, std::vector<xor_pair> &xor_assign);
    };
}
