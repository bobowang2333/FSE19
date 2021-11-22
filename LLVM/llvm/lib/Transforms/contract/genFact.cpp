/*** generate the facts of the IR ***/
/*** output in the SMT-LIB2 form ***/
/*** author: Jingbo Wang ***/

#include "genFact.h"
#include "llvm/IR/Instructions.h"
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
    genFact::genFact(raw_fd_ostream *os, std::map<Instruction*, int> &IDMap, std::vector<std::string> UNTAINT_VAR, std::vector<std::string> CONSTANT_VAR, std::vector<std::string> KEY_VAR, unsigned input_s, unsigned input_ind, unsigned input_num,unsigned input_bitset)
    {
        this->datalogFiles = os;
        this->IDMap = IDMap;
        this->UNTAINT_VAR = UNTAINT_VAR;
        this->CONSTANT_VAR = CONSTANT_VAR;
        this->KEY_VAR = KEY_VAR;
        this->input_s = input_s;
        this->input_ind = input_ind;  // the number of bits representing the input  (3 bits)
        this->input_num = input_num;  // the detailed number of the input variables (5)
        this->input_bitset = input_bitset;
        /** SMT LIB2 form **/
        useIntIDs = false;
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
        std::string fact;
        if(isa<Instruction>(ptr))
        {
            fact = createLoad(&I, I.getPointerOperand());
        }else{
            errs() << "[ERROR] Pointer Operand: " << *ptr << '\n';
        }
        writeFact(&I, fact);
    }

    void genFact::visitBinaryOperator(BinaryOperator &I)
    {
        /** extract two operands of this operator **/
        Value *op1 = I.getOperand(0);
        Value *op2 = I.getOperand(1);
        std::string fact1, fact2;
        if((isa<Instruction>(op1)) && (isa<Instruction>(op2)))
        {
            fact1 = createBinaryOp(&I, op1, "left");
            writeFact(&I, fact1);
            fact2 = createBinaryOp(&I, op2, "right");
            writeFact(&I, fact2);
        }
        /** IF op1 is not instr, it may be constant or name, which we use load_assign to represent the xor, and or op with constant operands **/
        else if((isa<Instruction>(op1)) && (!(isa<Instruction>(op2))))
        {
            fact1 = createBinaryConstant(&I, op1);
            writeFact(&I, fact1);
        }else if((isa<Instruction>(op2)) && (!(isa<Instruction>(op1))))
        {
            fact2 = createBinaryConstant(&I, op2);
            writeFact(&I, fact2);
        }
    }

    void genFact::visitStoreInst(StoreInst &I)
    {
        Value *val = I.getValueOperand();
        assert(val->getType() != NULL && "NULL Type being stored");
        Value *ptr = I.getPointerOperand();
        std::string fact;
        /** only both value and pointer are both instr, then we build this relation **/
        fact = createStore(ptr, val);
        if(fact.size())
            writeFact(&I, fact);
    }
    
    void genFact::visitTruncInst(TruncInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        fact = createTrunc(&I, op1);
        writeFact(&I, fact);
    }
    
    void genFact::visitZExtInst(ZExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        fact = createZExtInst(&I, op1);
        writeFact(&I, fact);
    }
    
    void genFact::visitICmpInst(ICmpInst &I)
    {
        /* for the imcp instruction: first op: type, second op: value1 third op: value2 */
        Instruction *inst = &I;
        User::op_iterator op_it;
        std::string fact;
        for(op_it = inst->op_begin(); op_it != inst->op_end(); op_it++)
        {
            Use *u = &*op_it;
            Value *v = u->get();
            if(isa<Instruction>(u))
            {
                fact = createICmpInst(&I, v);
                writeFact(&I, fact);
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
            fact = createAllocaInst(&I, alloc_name);
            writeFact(&I, fact);
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

    std::string genFact::createLoad(Value *to, Value *from)
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
            return createLoadAssign(toString, fromString);
        } else
        {
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
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
        if(!isa<Instruction>(from1))
        {
            type_v = from1;
            Instruction *from2_inst = cast<Instruction>(from2);
            int from2_num = IDMap[from2_inst];
            fromString = "#x" + ToBitVecForm(from2_num, input_s);
        }
        else //(!isa<Instruction>(from2))
        {
            type_v = from2;
            Instruction *from1_inst = cast<Instruction>(from1);
            int from1_num = IDMap[from1_inst];
            fromString = "#x" + ToBitVecForm(from1_num, input_s);
        }

        std::string fact;
        std::string var_name;
        if(type_v->hasName())
        {
            var_name = type_v->getName().str();
            unsigned r_s = UNTAINT_VAR.size();
            unsigned c_s = CONSTANT_VAR.size();
            unsigned k_s = KEY_VAR.size();
            if(std::find(UNTAINT_VAR.begin(), UNTAINT_VAR.end(), var_name) != UNTAINT_VAR.end())
            {
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (UNTAINT" + ' ' + fromString + "))" + "\n";
                unsigned rand_var_id_n = std::find(UNTAINT_VAR.begin(), UNTAINT_VAR.end(), var_name) - UNTAINT_VAR.begin();
                //unsigned iter_r = (rand_var_id_n) % 4;
                unsigned iter_r = 1 << (rand_var_id_n);
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned rand_time = (iter_r >> ((j - 1) * input_bitset)) & full;
                    std::string rand_var = "#b" + ToBitVecForm_original(rand_time, input_bitset);
                    fact = fact + "(rule (REC_UNTAINT_VAR" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                }
                return fact;
            }else if(std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) != CONSTANT_VAR.end())
            {
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (CONSTANT" + ' ' + fromString + "))" + "\n";
                unsigned cons_var_id_n = std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) - CONSTANT_VAR.begin();
                cons_var_id_n = cons_var_id_n + r_s + k_s;
                //unsigned iter_r = cons_var_id_n % 4;
                unsigned iter_r = 1 << (cons_var_id_n);
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    std::string zero_s = "#b" + ToBitVecForm_original(0, input_bitset);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned cons_time = (iter_r >> ((j - 1) * input_bitset)) & full;
                    std::string cons_var = "#b" + ToBitVecForm_original(cons_time, input_bitset);
                    fact = fact + "(rule (REC_UNTAINT_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + cons_var + ' ' + "))" + "\n";
                }
                return fact;
            }else{ 
                /** belongs to the key set **/
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (TAINT" + ' ' + fromString + "))" + "\n";
                unsigned key_var_id_n = std::find(KEY_VAR.begin(), KEY_VAR.end(), var_name) - KEY_VAR.begin();
                key_var_id_n = key_var_id_n + r_s;
                //unsigned iter_r = key_var_id_n % 4;
                unsigned iter_r = 1 << (key_var_id_n);
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    std::string zero_s = "#b" + ToBitVecForm_original(0, input_bitset);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned key_time = (iter_r >> ((j - 1) * input_bitset)) & full;
                    std::string key_var = "#b" + ToBitVecForm_original(key_time, input_bitset);
                    fact = fact + "(rule (REC_UNTAINT_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + key_var + ' ' + "))" + "\n";
                }
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
        (*datalogFiles) << getCommentMark() << ' ' << *v << '\n' << fact << '\n';
    }

    char genFact::getCommentMark() 
    {
        return ';';
    }
}
