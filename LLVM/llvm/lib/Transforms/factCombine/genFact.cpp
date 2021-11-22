/*** generate the facts of the IR ***/
/*** output in the SMT-LIB2 form ***/
/*** author: Jingbo Wang ***/

#include "genFact.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Metadata.h"
#include <string>
#include <iostream>
#include <sstream>
#include <fstream>
#include <bitset>
#include <algorithm>
#include <math.h>
#include <vector>
#include <iomanip>

namespace assign{
    genFact::genFact(raw_fd_ostream *os, raw_fd_ostream *keyFile, std::map<Instruction*, int> &IDMap, std::vector<std::string> &RAND_VAR, std::vector<std::string> &CONSTANT_VAR, std::vector<std::string> &KEY_VAR, unsigned input_s, unsigned input_ind, unsigned input_num,unsigned input_bitset, std::map<Instruction*, std::vector<unsigned>> &REC_ALL_INC, std::map<Instruction*, std::vector<unsigned>> &REC_RAND_VAR, std::map<unsigned, bool> &RAND_var, std::map<unsigned, bool> &KEY_SENSITIVE_var, std::map<unsigned, bool> &KEY_IND_var)
    {
        this->datalogFiles = os;
        this->keyFile = keyFile;
        this->IDMap = IDMap;
        this->RAND_VAR = RAND_VAR;
        this->CONSTANT_VAR = CONSTANT_VAR;
        this->KEY_VAR = KEY_VAR;
        this->input_s = input_s;
        this->input_ind = input_ind;  // the number of bits representing the input  (3 bits)
        this->input_num = input_num;  // the detailed number of the input variables (5)
        this->input_bitset = input_bitset;
        /** SMT LIB2 form **/
        useIntIDs = false;
        this->REC_ALL_INC = REC_ALL_INC;
        this->REC_RAND_VAR = REC_RAND_VAR;
        this->RAND_var = RAND_var;
        this->KEY_SENSITIVE_var = KEY_SENSITIVE_var;
        this->KEY_IND_var = KEY_IND_var;
        //this->F = F;
        (*os) << getCommentMark() << "### Begin facts \n";
    }

    std::string getFuncReturnName(StringRef funcName)
    {
        assert(funcName.size() && "Size of function name is zero");
        std::string ret = funcName;
        return ret + "_RETURN";
    }

    //to bit string
    std::string genFact::ToBitVecForm_original (unsigned in, unsigned max_len)
    {
        std::vector<int> tmp_bv;
        std::string res, rem_s;
        while(in != 0)
        {
            if(in & 1)
                tmp_bv.push_back(1);
            else
                tmp_bv.push_back(0);
            in >>= 1;
        }
        std::reverse(tmp_bv.begin(), tmp_bv.end());
        std::stringstream result;
        std::copy(tmp_bv.begin(), tmp_bv.end(), std::ostream_iterator<int>(result, ""));
        res = result.str();
        if(max_len >= tmp_bv.size())
        {
            unsigned rem = max_len - tmp_bv.size();
            unsigned it = 0;
            while(it != rem)
            {
                rem_s += "0";
                it++;
            }
            res = rem_s + res;
            return res;
        }else
        {
            std::string ERROR = ";the given length is less than the input value";
            return ERROR;
        }
    }
    
    //to hex string
    std::string genFact::ToBitVecForm(unsigned in, unsigned max_len)
    {
        if(max_len == 0)
        {
            std::string ERROR = ";the given length is less than the input value";
            return ERROR;
        }else{
            std::stringstream stream;
            stream << std::setfill('0') << std::setw(max_len/4) << std::hex << in;
            std::string ret = stream.str();
            stream.str("");
            stream.clear();
            return ret;
        }
    }
    
    
    void genFact::visitLoadInst(LoadInst &I)
    {
        Type *elementType = I.getType();
        assert(elementType && "NULL this type");

        Value *ptr = I.getPointerOperand();
        std::string fact, ret, type_output;
        if(isa<Instruction>(ptr))
        {
            fact = createLoad(&I, I.getPointerOperand());
            writeFact(&I, fact);
            ret = preCal_load(&I, I.getPointerOperand());
            //writeFact(&I, ret);
            
            /* type inference */
            //type_output = assign_type(&I, I.getPointerOperand());
            //writeType(type_output);
        }else{
            errs() << "[ERROR] Pointer Operand: " << *ptr << '\n';
        }
        //writeFact(&I, fact);
    }

    void genFact::visitBinaryOperator(BinaryOperator &I)
    {
        /** extract two operands of this operator **/
        Value *op1 = I.getOperand(0);
        Value *op2 = I.getOperand(1);
        std::string fact1, fact2;
        std::string REC, type_output, BV_RES;
        if((isa<Instruction>(op1)) && (isa<Instruction>(op2)))
        {
            fact1 = createBinaryOp(&I, op1, "left");
            writeFact(&I, fact1);
            fact2 = createBinaryOp(&I, op2, "right");
            writeFact(&I, fact2);
            REC = preCal_binary(&I, op1, op2);
            //writeFact(&I, REC);
            
            BV_RES = binary_type(&I, op1, op2);
            writeType(BV_RES);
            /** write the type for the direct type inference **/
            //type_output = binary_type(&I, op1, op2);
            //writeType(type_output);
        }
        /** IF op1 is not instr, it may be constant or name, which we use load_assign to represent the xor, and or op with constant operands **/
        else if((isa<Instruction>(op1)) && (!(isa<Instruction>(op2))))
        {
            fact1 = createBinaryConstant(&I, op1);
            writeFact(&I, fact1);
            REC = preCal_load(&I, op1);
            //writeFact(&I, REC);
            //type_output = assign_type(&I, op1);
            //writeType(type_output);
        }else if((isa<Instruction>(op2)) && (!(isa<Instruction>(op1))))
        {
            fact2 = createBinaryConstant(&I, op2);
            writeFact(&I, fact2);
            REC = preCal_load(&I, op2);
            //writeFact(&I, REC);
            //type_output = assign_type(&I, op2);
            //writeType(type_output);
        }else{
            std::cout << "Two operands are both constant" << std::endl;
        }
    }

    void genFact::visitStoreInst(StoreInst &I)
    {
        Value *val = I.getValueOperand();
        assert(val->getType() != NULL && "NULL Type being stored");
        Value *ptr = I.getPointerOperand();
        std::string fact, ret, type_output;
        /** only both value and pointer are both instr, then we build this relation **/
        fact = createStore(ptr, val);
        if(fact.size())
        {
            writeFact(&I, fact);
            if(isa<Instruction>(ptr) && isa<Instruction>(val))
            {
                ret = preCal_load(ptr, val);
                //writeFact(&I, ret);
                //type_output = assign_type(ptr, val);
                //writeType(type_output);
            }
        }
    }
    
    void genFact::visitTruncInst(TruncInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact, ret, type_output;
        fact = createTrunc(&I, op1);
        writeFact(&I, fact);
        ret = preCal_load(&I, op1);
        //writeFact(&I, ret);
        //type_output = assign_type(&I, op1);
        //writeType(type_output);
    }
    
    void genFact::visitZExtInst(ZExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact, ret, type_output;
        fact = createZExtInst(&I, op1);
        writeFact(&I, fact);
        ret = preCal_load(&I, op1);
        //writeFact(&I, ret);
        //type_output = assign_type(&I, op1);
        //writeType(type_output);
    }
    
    void genFact::visitSExtInst(SExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact, ret, type_output;
        fact = createSExtInst(&I, op1);
        writeFact(&I, fact);
        ret = preCal_load(&I, op1);
        //writeFact(&I, ret);
        //type_output = assign_type(&I, op1);
        //writeType(type_output);
    }
    
    void genFact::visitICmpInst(ICmpInst &I)
    {
        /* for the imcp instruction: first op: type, second op: value1 third op: value2 */
        Instruction *inst = &I;
        User::op_iterator op_it;
        std::string fact, ret, type_output;
        for(op_it = inst->op_begin(); op_it != inst->op_end(); op_it++)
        {
            Use *u = &*op_it;
            Value *v = u->get();
            if(isa<Instruction>(u))
            {
                fact = createICmpInst(&I, v);
                writeFact(&I, fact);
                ret = preCal_load(&I, v);
                //writeFact(&I, ret);
                //type_output = assign_type(&I, v);
                //writeType(type_output);
            }
        }
    }
    
    void genFact::visitAllocaInst(AllocaInst &I)
    {
        Instruction *inst = &I;
        std::string fact;
        if(inst->hasName())
        {
            std::string alloc_name = inst->getName().str();
            //fact = createAllocaInst(&I, alloc_name);
            //writeFact(&I, fact);
        }
    }
    
    void genFact::cal_XorAssign(Function &F, std::vector<xor_pair> &xor_assign)
    {
        for(inst_iterator it = inst_begin(F); it != inst_end(F); ++it)
        {
            Instruction *inst = &*it;
            const char *opcode_name = inst->getOpcodeName();
            std::string opName(opcode_name);
            if(!opName.compare("xor"))
            {
                int inst_num = IDMap[inst];
                std::string inst_str = "#x" + ToBitVecForm(inst_num, input_s);
                // for two operands of XOR
                Value *op1 = inst->getOperand(0);
                Value *op2 = inst->getOperand(1);
                if((isa<Instruction>(op1)) && (isa<Instruction>(op2)))
                {
                    Instruction *op1_inst = cast<Instruction>(op1);
                    Instruction *op2_inst = cast<Instruction>(op2);
                    int op1_num = IDMap[op1_inst];
                    int op2_num = IDMap[op2_inst];
                    std::string op1_str = "#x" + ToBitVecForm(op1_num, input_s);
                    std::string op2_str = "#x" + ToBitVecForm(op2_num, input_s);
                    xor_assign.push_back(std::make_tuple(inst_str, op1_str, op2_str));
                }
            }else
                continue;
        }
    }
    
    void genFact::cal_EqualAssign(Function &F, std::map<std::string, std::string> &new_equal_assign)
    {
        std::vector<equal_pair> equal_assign;
        std::map<std::string, bool> all_node;
        for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
        {
            Instruction *inst = &*i;
            int inst_num = IDMap[inst];
            std::string to_str = "#x" + ToBitVecForm(inst_num, input_s);
            std::string from_str;
            const char *opcode_name = inst->getOpcodeName();
            std::string opName(opcode_name);
            /** for the load, store zext trunc and icmp instr **/
            /*
            if(!opName.compare("store"))
            {
                StoreInst *inst_val = cast<StoreInst>(inst);
                Value *val = inst_val->getValueOperand();
                Value *ptr = inst_val->getPointerOperand();
                if(isa<Instruction>(ptr) && isa<Instruction>(val))
                {
                    Instruction *ptr_inst = cast<Instruction>(ptr);
                    Instruction *val_inst = cast<Instruction>(val);
                    to_str = "#x" + ToBitVecForm(IDMap[ptr_inst], input_s);
                    from_str = "#x" + ToBitVecForm(IDMap[val_inst], input_s);
                }else
                    continue;
            }
            else if(!opName.compare("load"))
            {
                LoadInst *inst_val = cast<LoadInst>(inst);
                Value *ptr = inst_val->getPointerOperand();
                if(isa<Instruction>(ptr))
                {
                    Instruction *ptr_inst = cast<Instruction>(ptr);
                    from_str = "#x" + ToBitVecForm(IDMap[ptr_inst], input_s);
                }else
                    continue;
            }
            else if((!opName.compare("zext")) || (!opName.compare("trunc")) || (!opName.compare("icmp")))
            {
                Value *op1 = inst->getOperand(0);
                if(isa<Instruction>(op1))
                {
                    Instruction *op1_inst = cast<Instruction>(op1);
                    from_str = "#x" + ToBitVecForm(IDMap[op1_inst], input_s);
                }else
                    continue;
            }else{
                continue;
            }
            */
            
            /** (equal_assign from1 from2) => (equal_assign from2 from1) **/
            /*
            equal_assign.push_back(std::make_tuple(to_str, from_str));
            equal_assign.push_back(std::make_tuple(from_str, to_str));
            */
            // insert all the nodes(variables) to a vector
            if((all_node.find(to_str)) == all_node.end())
                all_node.insert(std::pair<std::string, bool>(to_str, true));
            if(all_node.find(from_str) == all_node.end())
                all_node.insert(std::pair<std::string, bool>(from_str, true));
        }
        calEqualSet(F, new_equal_assign, all_node);
    }
    
     /** (=> (and (euqal_assign from1 from2) (equal_assign from2 from3)) (equal_assign from1 from3)) **/
    void genFact::calEqualSet(Function &F, std::map<std::string, std::string> &new_equal_assign, std::map<std::string, bool> &all_node){
        std::map<std::string, bool> marked;
        std::map<std::string, int> id;
        unsigned count = 0;
        // find in large vectors; sort at first, then do binary sort
        //std::sort(all_node.begin(), all_node.end());
        for(std::map<std::string, bool>::iterator it = all_node.begin(); it != all_node.end();++it){
            std::string op1 = it->first;
            std::vector<std::string> now_marked;
            if(marked.find(op1) == marked.end())
            {
                dfs(F, op1, marked, id, count, now_marked);
                count++;
                for(std::vector<std::string>::iterator nit = now_marked.begin(); nit != now_marked.end(); ++nit){
                    std::string str1 = *nit;
                    for(std::vector<std::string>::iterator mit = now_marked.begin(); mit != now_marked.end(); ++mit){
                        std::string str2 = *mit;
                        new_equal_assign.insert(std::pair<std::string, std::string>(str1, str2));
                    }
                }
            }
        }
        
        
        //build new equal_assign map by comparing the id are same or not
        // id same => two vertices are connected
        /*
        for(std::vector<std::string>::iterator it = all_node.begin(); it != all_node.end(); ++it)
        {
            int id1 = (id.find(*it))->second;
            // (=> true (equal_assign from1 from1))
            new_equal_assign.push_back(std::make_tuple(*it, *it));
            for(std::vector<std::string>::iterator ait = all_node.begin(); ait != all_node.end(); ++ait){
                int id2 = (id.find(*ait))->second;
                if(id1 == id2)
                {
                    if(std::find(new_equal_assign.begin(), new_equal_assign.end(), std::make_tuple(*it, *ait)) == new_equal_assign.end())
                        new_equal_assign.push_back(std::make_tuple(*it, *ait));
                    if(std::find(new_equal_assign.begin(), new_equal_assign.end(), std::make_tuple(*ait, *it)) == new_equal_assign.end())
                        new_equal_assign.push_back(std::make_tuple(*ait, *it));
                }
            }
        }
        */
    }
    
    void genFact::findEqual(Function &F, unsigned toFind, std::vector<unsigned> &res)
    {
        std::map<unsigned, bool> marked;
        equal_dfs(F, toFind, marked);
        
        //print out all the equivalent nodes
        for(std::map<unsigned, bool>::iterator it = marked.begin(); it != marked.end(); ++it){
            res.push_back(it->first);
        }
        
    }
    
    void genFact::equal_dfs(Function &F, unsigned toFind, std::map<unsigned, bool> &marked){
        marked.insert(std::pair<unsigned, bool>(toFind, true));
        std::vector<unsigned> adjacent;
        adjacent_node(F, adjacent, toFind);
        for(std::vector<unsigned>::iterator it = adjacent.begin(); it != adjacent.end(); ++it)
        {
            unsigned op1 = *it;
            if(marked.find(op1) == marked.end())
                equal_dfs(F, op1, marked);
            else
                continue;
        }
    }
    
    //previously version
    
    void genFact::dfs(Function &F, std::string node, std::map<std::string, bool> &marked, std::map<std::string, int> &id, unsigned count, std::vector<std::string> &now_marked){
        marked.insert(std::pair<std::string, bool>(node, true));
        now_marked.push_back(node);
        id.insert(std::pair<std::string, int>(node, count));
        std::vector<std::string> adjacent;
        //temporarily comment
        /*
        adjacent_node(F, adjacent, node);
        for(std::vector<std::string>::iterator it = adjacent.begin(); it != adjacent.end(); ++it)
        {
            std::string op1 = *it;
            if(marked.find(op1) == marked.end())
                dfs(F, op1, marked, id, count, now_marked);
            else
                continue;
        }
        */
    }
    
    void genFact::adjacent_node(Function &F, std::vector<unsigned> &adjacent, unsigned node)
    {
        for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
        {
            Instruction *inst = &*i;
            unsigned to_num, from_num;
            to_num = IDMap[inst];
            const char *opcode_name = inst->getOpcodeName();
            std::string opName(opcode_name);
            // not store and not load instr
            if((opName.compare("store")) && (opName.compare("load")))
                continue;
            else if (!opName.compare("store")){
                StoreInst *inst_val = cast<StoreInst>(inst);
                Value *val = inst_val->getValueOperand();
                Value *ptr = inst_val->getPointerOperand();
                if(isa<Instruction>(ptr) && isa<Instruction>(val))
                {
                    Instruction *ptr_inst = cast<Instruction>(ptr);
                    Instruction *val_inst = cast<Instruction>(val);
                    to_num = IDMap[ptr_inst];
                    from_num = IDMap[val_inst];
                    if((node != to_num) && (node != from_num))
                        continue;
                    else if (node == to_num){
                        adjacent.push_back(from_num);
                    }else{
                        adjacent.push_back(to_num);
                    }
                }else
                    continue;
            // load instr
            }else{
                LoadInst *inst_val = cast<LoadInst>(inst);
                Value *ptr = inst_val->getPointerOperand();
                if(isa<Instruction>(ptr))
                {
                    Instruction *ptr_inst = cast<Instruction>(ptr);
                    from_num = IDMap[ptr_inst];
                    if((to_num != node) && (from_num != node))
                        continue;
                    else if(to_num == node)
                        adjacent.push_back(from_num);
                    else
                        adjacent.push_back(to_num);
                }else
                    continue;

            }
          }
    }
    
    std::string genFact::createAllocaInst(Value *to, std::string alloc_name)
    {
        std::string fact;
        Instruction *to_inst = cast<Instruction>(to);
        int to_num = IDMap[to_inst];
        //std::string toString = "#b" + ToBitVecForm(to_num, input_s);
        /* print the corresponding ID in hexdecimal form */
        std::stringstream stream;
        stream << "#x" << std::setfill('0') << std::setw(input_s/4) << std::hex << to_num;
        std::string toString = stream.str();
        fact = ";(alloca " + toString + ' ' + alloc_name + " )";
        return fact;
    }
    
    std::string genFact::createICmpInst(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (icmp_assign " + toString + ' ' + fromString + "))";
        return fact;
    }

    std::string genFact::createTrunc(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (trunc_assign " + toString + ' ' + fromString + "))";
        return fact;
    }
    
    std::string genFact::createZExtInst(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (zext_assign " + toString + ' ' + fromString + "))";
        return fact;

    }
    
    std::string genFact::createSExtInst(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (sext_assign " + toString + ' ' + fromString + "))";
        return fact;
        
    }
    
    /**
    std::string genFact::createStore(Value *to, Value *from)
    {
        // example: %173:zext %x14, while %173 is the "to" and %x14 is "from"
        // "to" is always the instruction
        if(isa<Instruction>(from))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            int to_num = IDMap[to_inst];
            int from_num = IDMap[from_inst];
            std::string toString = "#b" + ToBitVecForm(to_num, input_s);
            std::string fromString = "#b" + ToBitVecForm(from_num, input_s);
            std::string fact;
            fact = createStoreAssign(toString, fromString);
            return fact;
        }
    }
    **/
    
    std::string genFact::assign_type(Value *to, Value *from)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        assert(from->getType() && "from value with NULL type");
        std::string ret;
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            unsigned to_num = IDMap[to_inst];
            unsigned from_num = IDMap[from_inst];
            
            // delete the value s (store destination s);
            const char *opcode_name = to_inst->getOpcodeName();
            std::string opcode_str(opcode_name);
            bool store_flag = false;
            if(!opcode_str.compare("store"))
                store_flag = true;
            bool LoadDelete = false;
            
            //test
            std::string test = "#x" + ToBitVecForm(to_num, input_s);
            if(!test.compare("#x052fd"))
                bool test = true;
            //bool LoadDelete = true;
            // delete the load x (load value x) which won't be used afterwards
            /*
            std::string test_str = "#x" + ToBitVecForm(to_num, input_s);
            bool test = false;
            if(!test_str.compare("#x013d9"))
                test = true;
            if(!opcode_str.compare("load"))
            {
                for(Value::use_iterator i = to_inst->use_begin(); i != to_inst->use_end(); ++i){
                    if(Instruction *found_inst= dyn_cast<Instruction>(*i)){
                        if(IDMap.find(found_inst) == IDMap.end())
                            break;
                        if(test) {
                            errs() << *to_inst << "\n";
                            errs() << *found_inst << "\n";
                        }
                        unsigned found_num = IDMap[found_inst];
                        if(found_num > to_num)
                        {
                            LoadDelete = false;
                            break;
                        }
                    }
                }
            }
            */
            
            // for deleting the redundant variable
            /*
            std::string test_str = "#x" + ToBitVecForm(to_num, input_s);
            if(!test_str.compare("#x0143c"))
                bool test_flag = true;
            if(!opcode_str.compare("load"))
            {
                //based on instr, get it's function
                Function *F = (to_inst->getParent())->getParent();
                std::vector<unsigned> equal_set;
                findEqual(*F, to_num, equal_set);
                //for(std::vector<unsigned>::iterator eit = equal_set.begin(); eit != equal_set.end(); ++eit)
                auto it = std::max_element(std::begin(equal_set), std::end(equal_set));
                if((*it) == to_num)
                    LoadDelete = true;
            }
            */
            if(RAND_var.find(from_num) != RAND_var.end())
            {
                RAND_var.insert(std::pair<unsigned, bool>(to_num, true));
                ret = "RAND #x" + ToBitVecForm(to_num, input_s) + "\n";
                if(store_flag || LoadDelete)
                {
                    RAND_var.erase(from_num);
                    //erase the REC_RAND_VAR
                    REC_RAND_VAR.erase(from_inst);
                }
            }else if(KEY_SENSITIVE_var.find(from_num) != KEY_SENSITIVE_var.end())
            {
                KEY_SENSITIVE_var.insert(std::pair<unsigned, bool>(to_num, true));
                ret = "KEY_SENSITIVE #x" + ToBitVecForm(to_num, input_s) + "\n";
                //write to keyFile
                writeKey("#x"+ToBitVecForm(to_num, input_s));
                if(store_flag || LoadDelete)
                    KEY_SENSITIVE_var.erase(from_num);
            }else if(KEY_IND_var.find(from_num) != KEY_IND_var.end())
            {
                KEY_IND_var.insert(std::pair<unsigned, bool>(to_num, true));
                ret = "KEY_IND #x" + ToBitVecForm(to_num, input_s) + "\n";
                if(store_flag || LoadDelete)
                    KEY_IND_var.erase(from_num);
            }else
            {
                ret = "ERROR: #x" + ToBitVecForm(to_num, input_s) + "it doesn't belong to any type\n";
            }
            
            if(store_flag || LoadDelete)
            {
                REC_ALL_INC.erase(from_inst);
            }
            return ret;
        }
    }
    
    std::string genFact::binary_type(Value *to, Value *from1, Value *from2)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from1_inst = cast<Instruction>(from1);
        Instruction *from2_inst = cast<Instruction>(from2);
        unsigned to_num = IDMap[to_inst];
        unsigned from1_num = IDMap[from1_inst];
        unsigned from2_num = IDMap[from2_inst];
        std::string to_str = "#x" + ToBitVecForm(to_num, input_s);
        std::string from1_str = "#x" + ToBitVecForm(from1_num, input_s);
        std::string from2_str = "#x" + ToBitVecForm(from2_num, input_s);
        std::string zerobit = "#b" + ToBitVecForm_original(0, input_bitset);
        std::string onebit = "#b" + ToBitVecForm_original(1, input_bitset);
        std::string ret;
        /** check the opcode of result operand **/
        const char *opcode_name = to_inst->getOpcodeName();
        std::string opName(opcode_name);
        /** for XOR **/
        /** [RAND] + [ANY TYPE] **/

        if(!opName.compare("xor"))
        {
            ret = "; XOR-> BV_DIFF_REC, BV_SAME_REC, BV_ALL_INTERSECT info\n";
            //calculate the BV_DIFF_REC information
            if((REC_RAND_VAR.find(from1_inst) != REC_RAND_VAR.end()) || (REC_RAND_VAR.find(from2_inst) != REC_RAND_VAR.end()))
            {
                if(!BV_DIFF_REC(from1_inst, from2_inst))
                    ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                else if(!BV_DIFF_REC(from2_inst, from1_inst))
                    ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + onebit + "))\n";
                else{
                    ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + zerobit + "))\n";
                    ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                    //calculate the BV_SAME_REC info
                    if(BV_SAME_REC(from1_inst, from2_inst))
                        ret = ret + "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                    else
                        ret = ret +  "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                }
            }else{
            // calculate the BV_ALL_INTERSECT
            if(BV_ALL_INTERSECT(from1_inst, from2_inst))
                ret = ret + "(rule (BV_ALL_INTERSECT " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
            else
                ret = ret + "(rule (BV_ALL_INTERSECT " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
            if(BV_SAME_REC(from1_inst, from2_inst))
                ret = ret + "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
            else
                ret = ret +  "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
            }
            /** for the andor operator or other operators else **/
        }else{
            /** [RAND] + [SID] **/
            ret = "; ANDOR -> BV_DIFF_REC, BV_SAME_REC, BV_ALL_INTERSECT info\n";
            if((REC_RAND_VAR.find(from1_inst) != REC_RAND_VAR.end()) && (REC_RAND_VAR.find(from2_inst) != REC_RAND_VAR.end())) // RAND && RAND
            {
                // calculate the BV_DIFF_REC info
                if(!BV_DIFF_REC(from1_inst, from2_inst))
                    ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                else if (!BV_DIFF_REC(from2_inst, from1_inst)){
                    ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + onebit + "))\n";
                }else{
                    ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + zerobit + "))\n";
                    ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                    if(BV_SAME_REC(from1_inst, from2_inst))
                        ret = ret + "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                    else
                        ret = ret +  "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                }
            }else{// calculate the BV_ALL_INTERSECT
                if(BV_ALL_INTERSECT(from1_inst, from2_inst))
                    ret = ret + "(rule (BV_ALL_INTERSECT " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                else{
                    ret = ret + "(rule (BV_ALL_INTERSECT " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                    //newly added for AES version
                    if((REC_RAND_VAR.find(from1_inst) != REC_RAND_VAR.end()) && (!BV_DIFF_REC(from1_inst, from2_inst)))
                        ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
                    else
                        ret = ret + "(rule (BV_DIFF_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                    if((REC_RAND_VAR.find(from2_inst) != REC_RAND_VAR.end()) && (!BV_DIFF_REC(from2_inst, from1_inst)))
                        ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + onebit + "))\n";
                    else
                        ret = ret + "(rule (BV_DIFF_REC " + from2_str + ' ' + from1_str + ' ' + zerobit + "))\n";
                }
                if(BV_SAME_REC(from1_inst, from2_inst))
                    ret = ret + "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + zerobit + "))\n";
                else
                    ret = ret +  "(rule (BV_SAME_REC " + from1_str + ' ' + from2_str + ' ' + onebit + "))\n";
            }
        }
        // remove the two elements which are operands of andor OR xor

        REC_ALL_INC.erase(from1_inst);
        REC_ALL_INC.erase(from2_inst);
        if(REC_RAND_VAR.find(from1_inst) != REC_RAND_VAR.end())
            REC_RAND_VAR.erase(from1_inst);
        if(REC_RAND_VAR.find(from2_inst) != REC_RAND_VAR.end())
            REC_RAND_VAR.erase(from2_inst);
        return ret;
    }
    
    bool genFact::BV_DIFF_REC(Instruction *from1, Instruction *from2)
    {
        unsigned from1_num = IDMap[from1];
        unsigned from2_num = IDMap[from2];
        std::vector<unsigned> rand_from1, all_from2;
        if(REC_RAND_VAR.find(from1) != REC_RAND_VAR.end())
            rand_from1 = (REC_RAND_VAR.find(from1))->second;
        if(REC_ALL_INC.find(from2) != REC_ALL_INC.end())
            all_from2 = (REC_ALL_INC.find(from2))->second;
        std::set<unsigned> res;
        std::set<unsigned>::iterator it;
        std::set_difference(rand_from1.begin(), rand_from1.end(), all_from2.begin(), all_from2.end(), std::inserter(res, res.end()));
        if(res.empty())
            return true;
        else
            return false;

        /*
        std::vector<unsigned> res;
        for(std::set<unsigned>::iterator it = rand_from1.begin(); it != rand_from1.end(); it++)
        {
            if(std::find(all_from2.begin(), all_from2.end(), *it) != all_from2.end())
                continue;
            else
                res.push_back(*it);
        }
        if(res.empty())
            return true;
        else
            return false;
        */
    }
    
    bool genFact::BV_SAME_REC(Instruction *from1, Instruction *from2)
    {
        std::vector<unsigned> all_from1, all_from2;
        if(REC_ALL_INC.find(from1) != REC_ALL_INC.end())
            all_from1 = (REC_ALL_INC.find(from1))->second;
        if(REC_ALL_INC.find(from2) != REC_ALL_INC.end())
            all_from2 = (REC_ALL_INC.find(from2))->second;
        
        std::sort(all_from1.begin(), all_from1.end());
        std::sort(all_from2.begin(), all_from2.end());
        return(all_from1 == all_from2);
        /*
        //compare if two vectors are same or not
        bool not_equal = false;
        if(all_from1.size() != all_from2.size())
            return false;
        for(std::vector<unsigned>::iterator it = all_from1.begin(); it != all_from1.end(); it++)
        {
            if(std::find(all_from2.begin(), all_from2.end(), *it) == all_from2.end())
            {
                bool not_equal = true;
                break;
            }
        }
        if(not_equal)
            return false;
        else
            return true;
         */
    }
    
    bool genFact::BV_ALL_INTERSECT(Instruction *from1, Instruction *from2)
    {
        std::vector<unsigned> all_1, all_2;
        if(REC_ALL_INC.find(from1) != REC_ALL_INC.end())
            all_1 = (REC_ALL_INC.find(from1))->second;
        if(REC_ALL_INC.find(from2) != REC_ALL_INC.end())
            all_2 = (REC_ALL_INC.find(from2))->second;
        std::vector<unsigned> intersect;
        std::set_intersection(all_1.begin(), all_1.end(), all_2.begin(),all_2.end(), std::back_inserter(intersect));
        if(intersect.empty())
            return true;
        else
            return false;

    }

    std::string genFact::createLoad(Value *to, Value *from)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        assert(from->getType() && "from value with NULL type");
        std::string ret;
        //assert(from->getType()->isPointerTy() && "from value that is not a pointer");
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            int to_num = IDMap[to_inst];
            int from_num = IDMap[from_inst];
            std::string toString = "#x" + ToBitVecForm(to_num, input_s);
            std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
            return createLoadAssign(toString, fromString);
        } else
        {
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
    }
    
    std::string genFact::preCal_load(Value *to, Value *from)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        assert(from->getType() && "from value with NULL type");
        std::string ret;
        bool store_flag = false;
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            const char *opcode_name = to_inst->getOpcodeName();
            std::string opcode_str(opcode_name);
            if(!opcode_str.compare("store"))
                store_flag = true;
            std::vector<unsigned> to_all, to_rand;
            if(REC_ALL_INC.find(from_inst) != REC_ALL_INC.end())
            {
                to_all = (REC_ALL_INC.find(from_inst))->second;
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, to_all));
                //ret = write(to_inst, to_all, 1);
            }else
            {
                //ret = writeZero(to_inst, 0);
            }
            if(REC_RAND_VAR.find(from_inst) != REC_RAND_VAR.end())
            {
                to_rand = (REC_RAND_VAR.find(from_inst))->second;
                // Jun 30 Added for testing
                std::string to_inst_id = ToBitVecForm(IDMap[to_inst], 20);
                if(!to_inst_id.compare("05109"))
                    std::cout << "TEST: to_inst ID is [" << to_inst_id << "]" << std::endl;
                REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, to_rand));
                //ret = ret + write(to_inst, to_rand, 0);
            }
            // if the loaded variable is not random type, then we don't print out the information
            else{
                //ret = ret + writeZero(to_inst, 1);
            }
            //delete the stored value

            if(store_flag)
            {
                if(REC_RAND_VAR.find(from_inst) != REC_RAND_VAR.end())
                    REC_RAND_VAR.erase(from_inst);
                if(REC_ALL_INC.find(from_inst) != REC_ALL_INC.end())
                    REC_ALL_INC.erase(from_inst);
            }
            
            return ret;
        }else{
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
    }
    
    // type 1 => all_rec, type 0 => rand_var
    std::string genFact::write(Instruction *inst, std::vector<unsigned> &type_var, unsigned type)
    {
        unsigned inst_id = IDMap[inst];
        std::string instString = "#x" + ToBitVecForm(inst_id, input_s);
        unsigned res = 0;
        std::string ret;
        std::string type_prefix;
        if(type)
            type_prefix = "(rule (REC_ALL_INC ";
        else
            type_prefix = "(rule (REC_RAND_VAR ";
        //convert the integer to different times in REC_RAND_VAR
        unsigned type_time;
        for(unsigned j = 1; j <= input_num; j++)
        {
            std::string index = "#b" + ToBitVecForm_original(j, input_ind);
            type_time = calRange(j, type_var);
            std::string type_str = "#b" + ToBitVecForm_original(type_time, input_bitset);
            if(j == 1)
                ret = type_prefix + ' ' + instString + ' ' + index + ' ' + type_str + "))" + "\n";
            else
                ret = ret + type_prefix + ' ' + instString + ' ' + index + ' ' + type_str + "))" + "\n";
        }
        return ret;
    }
    
    unsigned genFact::calRange(unsigned j, std::vector<unsigned> &type_var)
    {
        unsigned tmp = 0;
        unsigned res = 0;
        unsigned full = (1 << input_bitset) - 1;
        for(std::vector<unsigned>::iterator it = type_var.begin(); it != type_var.end(); ++it)
        {
            if(((*it) >= ((j-1)*input_bitset)) && ((*it) < (j*input_bitset)))
            {
                tmp = ((*it) - ((j-1)*input_bitset));
                res = res | (1 << tmp);
            }
            else
                res = res | 0;
        }
        return res&full;
    }
    
    // for the non-rand variables, whose REC_RAND_VAR should be empty
    // type 0 ---> REC_ALL_INC, type 1---> REC_RAND_VAR
    std::string genFact::writeZero(Instruction *inst, unsigned type)
    {
        unsigned inst_id = IDMap[inst];
        std::string instString = "#x" + ToBitVecForm(inst_id, input_s);
        std::string ret, type_prefix;
        if(type)
            type_prefix = "(rule (REC_RAND_VAR ";
        else
            type_prefix = "(rule (REC_ALL_INC ";
        for(unsigned j = 1; j <= input_num; j++)
        {
            std::string index = "#b" + ToBitVecForm_original(j, input_ind);
            std::string rand_var = "#b" + ToBitVecForm_original(0, input_bitset);
            if(j == 1)
                ret = type_prefix + ' ' + instString + ' ' + index + ' ' + rand_var + "))" + "\n";
            else
                ret = ret + type_prefix + ' ' + instString + ' ' + index + ' ' + rand_var + "))" + "\n";
        }
        return ret;
    }

    std::string genFact::createBinaryConstant(Value *to, Value *from)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        assert(from->getType() && "from value with NULL type");
        //assert(from->getType()->isPointerTy() && "from value that is not a pointer");
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            int to_num = IDMap[to_inst];
            int from_num = IDMap[from_inst];
            std::string toString = "#x" + ToBitVecForm(to_num, input_s);
            std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
            std::string fact;
            fact = "(rule (binary_constant " + toString + " " + fromString + "))";
            return fact;
        } else
        {
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
    }
    
    std::string genFact::createBinaryOp(Value *to, Value *from, std::string OP_ID)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        if((isa<Instruction>(to)))
        {
            if(isa<Instruction>(from))
            {
                Instruction *to_inst = cast<Instruction>(to);
                int to_num = IDMap[to_inst];
                std::string toString = "#x" + ToBitVecForm(to_num, input_s);
                Instruction *from_inst = cast<Instruction>(from);
                int from_num = IDMap[from_inst];
                std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
                /** differ from the "xor" and other opcodes **/
                const char *opcode_name = to_inst->getOpcodeName();
                std::string opName(opcode_name);
                if(!opName.compare("xor"))
                {
                    return createXor(toString, fromString, OP_ID);
                }else //if ((!opName.compare("and")) || (!opName.compare("or")))
                {
                    return createAndOr(toString, fromString, OP_ID);
                }
                //else {
                  //  return createAssign(toString, fromString);
                //}
            }
        }
        else{
            errs() << "[ERROR] the operand of binary op is not Instruction" << '\n';
        }
    }
    
    //type 0 -> XOR, type 1 -> AND OR operation
    std::string genFact::preCal_binary(Value *to, Value *from1, Value *from2)
    {
        Instruction *to_inst = cast<Instruction>(to);
        const char *opcode_name = to_inst->getOpcodeName();
        std::string opName(opcode_name);
        unsigned type;
        if(!opName.compare("xor"))
            type = 0;
         else
             type = 1;
        unsigned to_num = IDMap[to_inst];
        Instruction *from1_inst = cast<Instruction>(from1);
        Instruction *from2_inst = cast<Instruction>(from2);
        // for the result operand's REC_ALL_INC
        std::vector<unsigned> res_all, res_rand;
        std::vector<unsigned> from1_all, from2_all;
        if(REC_ALL_INC.find(from1_inst) != REC_ALL_INC.end())
            from1_all = (REC_ALL_INC.find(from1_inst))->second;
        if(REC_ALL_INC.find(from2_inst) != REC_ALL_INC.end())
            from2_all = (REC_ALL_INC.find(from2_inst))->second;
        // for the result operand's REC_RAND_VAR, if they are in the map then the vector won't be empty else empty
        std::vector<unsigned> from1_rand, from2_rand;
        if(REC_RAND_VAR.find(from1_inst) != REC_RAND_VAR.end())
            from1_rand = (REC_RAND_VAR.find(from1_inst))->second;
        if(REC_RAND_VAR.find(from2_inst) != REC_RAND_VAR.end())
            from2_rand = (REC_RAND_VAR.find(from2_inst))->second;
        // set the REC_RAND_VAR and REC_ALL_INC of the result operand
        if(type){
            res_all = SetOr(from1_all, from2_all);
            REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, res_all));
        }
        else
        {
            res_all = XOR_ALL_INC(from1_all, from2_all, from1_rand, from2_rand);
            REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, res_all));
            if(!(from1_rand.empty() && from2_rand.empty()))
            {
                res_rand = XOR_RAND_VAR(from1_rand, from2_rand);
                // Jun 30 Added for testing
                std::string to_inst_id = ToBitVecForm(IDMap[to_inst], 20);
                if(!to_inst_id.compare("05109"))
                    std::cout << "TEST: to_inst ID is [" << to_inst_id << "]" << std::endl;
                if(!((from1_rand.size() == from2_rand.size()) && (std::equal(from1_rand.begin(), from1_rand.begin() + from1_rand.size(), from2_rand.begin()))))
                    REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, res_rand));
            }
            //else => the res_rand is empty Cz both operands are not rand
        }
        
        //write to file
        /*
        std::string ret;
        //write the final REC_RAND_VAR and REC_ALL_INC info to output smt file
        // ==> REC_ALL_INC at first
        ret = write(to_inst, res_all, 1);
        // ==> REC_RAND_VAR at second
        if(!res_rand.empty())
        {
            ret = ret + write(to_inst, res_rand, 0);
        }else
        {
            ret = ret + writeZero(to_inst, 1); // for the empty rand_var set
        }
        return ret;
        */
    }
    
    std::vector<unsigned> genFact::SetOr(std::vector<unsigned> &a, std::vector<unsigned> &b)
    {
        /*
        // for vector
        std::vector<unsigned> res;
        for(std::vector<unsigned>::iterator it = a.begin(); it != a.end(); ++it)
        {
            res.push_back(*it);
        }
        for(std::vector<unsigned>::iterator it = b.begin(); it != b.end(); it++)
        {
            if(std::find(res.begin(), res.end(), (*it)) == res.end())
                res.push_back(*it);
            else
                continue;
        }
        */
        std::vector<unsigned> res;
        std::vector<unsigned>::iterator it;
        std::sort(a.begin(), a.end());
        std::sort(b.begin(), b.end());
        std::set_union(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(res));
 
        return res;
    }
    
    std::vector<unsigned> genFact::XOR_ALL_INC(std::vector<unsigned> &all_1, std::vector<unsigned> &all_2, std::vector<unsigned> &rand_1, std::vector<unsigned> &rand_2)
    {
        /*
        // for vector
        std::vector<unsigned> intersect;
        set_intersection(rand_1.begin(), rand_1.end(), rand_2.begin(),rand_2.end(), std::inserter(intersect,intersect.begin()));
        std::vector<unsigned> tmp1, tmp2, ret;
        // for the from1 which removes the intersection
        for(std::vector<unsigned>::iterator it = all_1.begin(); it != all_1.end(); ++it)
        {
            if(std::find(intersect.begin(), intersect.end(), (*it)) != intersect.end())
                continue;
            else
                tmp1.push_back(*it);
        }
        // for the from2 which removes the intersection
        for(std::vector<unsigned>::iterator it = all_2.begin(); it != all_2.end(); ++it)
        {
            if(std::find(intersect.begin(), intersect.end(), (*it)) != intersect.end())
                continue;
            else
                tmp2.push_back(*it);
        }
        
        ret = SetOr(tmp1, tmp2);
        return ret;
        */
        std::vector<unsigned> ret, intersect, or_res;
        std::vector<unsigned>::iterator it;
        std::sort(rand_1.begin(), rand_1.end());
        std::sort(rand_2.begin(), rand_2.end());
        std::set_intersection(rand_1.begin(), rand_1.end(), rand_2.begin(), rand_2.end(), std::back_inserter(intersect));
 
        or_res = SetOr(all_1, all_2);
        std::sort(or_res.begin(), or_res.end());
        std::set_difference(or_res.begin(), or_res.end(), intersect.begin(), intersect.end(), std::back_inserter(ret));
        return ret;
    }
    
    std::vector<unsigned> genFact::XOR_RAND_VAR(std::vector<unsigned> &rand_1, std::vector<unsigned> &rand_2)
    {
        /*
        std::vector<unsigned> intersect, ret;
        set_intersection(rand_1.begin(), rand_1.end(), rand_2.begin(),rand_2.end(), std::inserter(intersect,intersect.begin()));
        for(std::vector<unsigned>::iterator it = rand_1.begin(); it != rand_1.end(); ++it)
        {
            if(std::find(intersect.begin(), intersect.end(), (*it)) != intersect.end())
                continue;
            else
                ret.push_back(*it);
        }
        for(std::vector<unsigned>::iterator it = rand_2.begin(); it != rand_2.end(); ++it)
        {
            if(std::find(intersect.begin(), intersect.end(), (*it)) != intersect.end())
                continue;
            else
                ret.push_back(*it);
        }
        return ret;
         */
        std::vector<unsigned> ret;
        std::vector<unsigned>::iterator it;
        std::set_symmetric_difference (rand_1.begin(), rand_1.end(), rand_2.begin(), rand_2.end(), std::back_inserter(ret));

        return ret;
    }

    /** for zext inst, the fact is directly written in the datalog file **/
    std::string genFact::createStore(Value *from1, Value *from2)
    {
        assert(from1 && "from1: NULL passed");
        assert(from2 && "from2: NULL passed");
        /** if "from1" is a name, then we don;t build the relation in this instr, but "from2" must be a instr **/
        if(isa<Instruction>(from1) && isa<Instruction>(from2))
        {
            Instruction *from1_inst = cast<Instruction>(from1);
            Instruction *from2_inst = cast<Instruction>(from2);
            int from1_num = IDMap[from1_inst];
            int from2_num = IDMap[from2_inst];
            std::string from1String = "#x" + ToBitVecForm(from1_num, input_s);
            std::string from2String = "#x" + ToBitVecForm(from2_num, input_s);
            std::string fact;
            fact = "(rule (store_assign " + from1String + ' ' + from2String + "))";
            return fact;
        }
        Value *type_v;
        std::string fromString;
        Instruction *inst_real;
        if(!isa<Instruction>(from1))
        {
            type_v = from1;
            Instruction *from2_inst = cast<Instruction>(from2);
            inst_real = from2_inst;
            unsigned from2_num = IDMap[from2_inst];
            fromString = "#x" + ToBitVecForm(from2_num, input_s);
        }
        else //(!isa<Instruction>(from2))
        {
            type_v = from2;
            Instruction *from1_inst = cast<Instruction>(from1);
            inst_real = from1_inst;
            unsigned from1_num = IDMap[from1_inst];
            fromString = "#x" + ToBitVecForm(from1_num, input_s);
        }

        std::string fact;
        std::string var_name;
        std::vector<unsigned> integter_ind;
        if(type_v->hasName())
        {
            var_name = type_v->getName().str();
            unsigned r_s = RAND_VAR.size();
            unsigned c_s = CONSTANT_VAR.size();
            unsigned k_s = KEY_VAR.size();
            if(std::find(RAND_VAR.begin(), RAND_VAR.end(), var_name) != RAND_VAR.end())
            {
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (RAND" + ' ' + fromString + "))" + "\n";
                //print out the type
                std::string type_output = "RAND " + fromString + "\n";
                //writeType(type_output);
                unsigned rand_var_id_n = std::find(RAND_VAR.begin(), RAND_VAR.end(), var_name) - RAND_VAR.begin();
                unsigned rand_time, remain;
                if(!fromString.compare("#x00178"))
                    bool test = true;
                /*
                // for pre_cal printing information
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    unsigned full = (1 << input_bitset) - 1;
                    if((rand_var_id_n < j*input_bitset) && (rand_var_id_n >= ((j-1)*input_bitset)))
                    {
                        remain = 1 << (rand_var_id_n - ((j-1)*input_bitset));
                        rand_time = remain & full;
                    }
                    else
                         rand_time = 0;
                    std::string rand_var = "#b" + ToBitVecForm_original(rand_time, input_bitset);
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                }
                */
                integter_ind.push_back(rand_var_id_n);
                // define the type of the input value
                RAND_var.insert(std::pair<unsigned, bool>(IDMap[inst_real], true));
                // Jun 30 Added for testing
                std::string inst_real_id = ToBitVecForm(IDMap[inst_real], 20);
                if(!inst_real_id.compare("05109"))
                    std::cout << "TEST: to_inst ID is [" << inst_real_id << "]" << std::endl;
                REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                return fact;
            }else if(std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) != CONSTANT_VAR.end())
            {
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (CONSTANT" + ' ' + fromString + "))" + "\n";
                // print out the type
                std::string type_output = "CONSTANT " + fromString + "\n";
                //writeType(type_output);
                unsigned cons_var_id_n = std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) - CONSTANT_VAR.begin();
                cons_var_id_n = cons_var_id_n + r_s + k_s;
                /*
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    std::string zero_s = "#b" + ToBitVecForm_original(0, input_bitset);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned cons_time, remain;
                    if((cons_var_id_n < j*input_bitset) && (cons_var_id_n >= ((j-1)*input_bitset)))
                    {
                        remain = 1 << (cons_var_id_n - ((j-1)*input_bitset));
                        cons_time = remain & full;
                    }else
                        cons_time = 0;
                    std::string cons_var = "#b" + ToBitVecForm_original(cons_time, input_bitset);
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + cons_var + ' ' + "))" + "\n";
                }
                */
                integter_ind.push_back(cons_var_id_n);
                // define the type of the input value
                KEY_IND_var.insert(std::pair<unsigned, bool>(IDMap[inst_real], true));
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                return fact;
            }else{ 
                /** belongs to the key set **/
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (KEY_SENSITIVE" + ' ' + fromString + "))" + "\n";
                // print out the type
                std::string type_output = "KEY_SENSITIVE " + fromString + "\n";
                //writeType(type_output);
                //write to the keyFile
                writeKey(fromString);
                unsigned key_var_id_n = std::find(KEY_VAR.begin(), KEY_VAR.end(), var_name) - KEY_VAR.begin();
                key_var_id_n = key_var_id_n + r_s;
                /*
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    std::string zero_s = "#b" + ToBitVecForm_original(0, input_bitset);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned key_time, remain;
                    if((key_var_id_n < j*input_bitset) && (key_var_id_n >= ((j-1)*input_bitset)))
                    {
                        remain = 1 << (key_var_id_n - ((j-1)*input_bitset));
                        key_time = remain & full;
                    }else
                        key_time = 0;
                    std::string key_var = "#b" + ToBitVecForm_original(key_time, input_bitset);
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + key_var + ' ' + "))" + "\n";
                }
                */
                integter_ind.push_back(key_var_id_n);
                // define the type of the input value
                KEY_SENSITIVE_var.insert(std::pair<unsigned, bool>(IDMap[inst_real], true));
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                /** intial convert version **/
                //std::string key_var = "#b" + std::bitset<input_s>(key_var_id).to_string();
                return fact;
            }
        }
    } 

    std::string genFact::createAssign(std::string to, std::string from)
    {
        std::string ret;
        /** use integter counting to represent the instrs and variables **/
        ret = "(rule (assign " + to + ' ' + from + "))";
        assert(ret.size());
        return ret;
    }

    std::string genFact::createLoadAssign(std::string to, std::string from)
    {
        std::string ret;
        ret = "(rule (load_assign " + to + ' ' + from + "))";
        assert(ret.size());
        return ret;
    }

    std::string genFact::createStoreAssign(std::string to, std::string from)
    {
        std::string ret;
        ret = "(rule (store_assign " + to + ' ' + from + "))";
        assert(ret.size());
        return ret;
    }


    std::string genFact::createXor(std::string to, std::string from, std::string OP_ID)
    {
        std::string ret;
        ret = "(rule (xor_assign_" +  OP_ID + ' ' + to + ' ' + from + "))";
        assert(ret.size());
        return ret;
    }
    

    std::string genFact::createAndOr(std::string to, std::string from, std::string OP_ID)
    {
        std::string ret;
        ret = "(rule (andor_assign_" + OP_ID + ' ' + to + ' ' + from + "))";
        assert(ret.size());
        return ret;
    }

    void genFact::writeFact(Value *v, std::string fact)
    {
        assert(fact.size() && "empty string passed to this func");
        assert(v && "NULL Value passed");
        //(*datalogFiles) << getCommentMark() << ' ' << *v << '\n' << fact << '\n';
        (*datalogFiles) << fact << '\n';
    }
    
    void genFact::writeType(std::string fact)
    {
        assert(fact.size() && "empty string passed to this func");
        (*datalogFiles) << fact;
    }
    
    void genFact::writeKey(std::string key)
    {
        assert(key.size() && "empty string passed to this func");
        (*keyFile) << key << "\n";
    }

    char genFact::getCommentMark() 
    {
        return ';';
    }
}
