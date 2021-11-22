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
    genFact::genFact(raw_fd_ostream *os, std::map<Instruction*, int> IDMap, std::vector<std::string> RAND_VAR, std::vector<std::string> CONSTANT_VAR, std::vector<std::string> KEY_VAR, unsigned input_s, unsigned input_ind, unsigned input_bitset)
    {
        this->datalogFiles = os;
        this->IDMap = IDMap;
        this->RAND_VAR = RAND_VAR;
        this->CONSTANT_VAR = CONSTANT_VAR;
        this->KEY_VAR = KEY_VAR;
        this->input_s = input_s;
        this->input_ind = input_ind;  // the number of bits representing the input  (3 bits)
        //this->input_num = input_num;  // the detailed number of the input variables (5)
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

    // to bit string
    /*
    std::string genFact::ToBitVecForm (unsigned in, unsigned max_len)
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
        unsigned rem = max_len - tmp_bv.size();
        unsigned it = 0;
        while(it != rem)
        {
            rem_s += "0";
            it++;
        }
        res = rem_s + res;
        return res;
    }
    */
    
    // to hex string
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
        writeFact(&I, fact);
    }
    
    void genFact::visitTruncInst(TruncInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        fact = createTrunc(&I, op1);
        writeFact(&I, fact);
    }
    
    void genFact::visitSExtInst(SExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        fact = createSExtInst(&I, op1);
        writeFact(&I, fact);
    }
    
    void genFact::visitZExtInst(ZExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        fact = createSExtInst(&I, op1);
        writeFact(&I, fact);
    }

    void genFact::visitGetElementPtrInst(GetElementPtrInst &I)
    {
        //array_base
        Value *arr_base = I.getOperand(0);
        Value *arr_index = I.getOperand(1);
        if(isa<Instruction>(arr_base))
        {
            unsigned type = 0; // 0-> the base address of the array
            std::string fact;
            fact = createGetElementPtrInst(&I, arr_base, type);
            writeFact(&I, fact);
        }
        if(isa<Instruction>(arr_index))
        {
            unsigned type = 1; // 1-> the index of the array
            std::string fact;
            fact = createGetElementPtrInst(&I, arr_index, type);
            writeFact(&I, fact);
        }
    }
    
    void genFact::visitIntToPtrInst(IntToPtrInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        if(isa<Instruction>(op1))
        {
            fact = createSExtInst(&I, op1);
            writeFact(&I, fact);
        }
    }
    
    void genFact::visitBitCastInst(BitCastInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact;
        if(isa<Instruction>(op1))
        {
            fact = createSExtInst(&I, op1);
            writeFact(&I, fact);
        }
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
        //std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        /* print the corresponding ID in hexdecimal form */
        std::stringstream stream;
        stream << "#x" << std::setfill('0') << std::setw(input_s/4) << std::hex << to_num;
        std::string toString = stream.str();
        fact = ";(alloca " + toString + ' ' + alloc_name + " )";
        stream.str("");
        stream.clear();
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
    
    std::string genFact::createBitCast(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (bitCast " + toString + ' ' + fromString + "))";
        return fact;
    }

    std::string genFact::createGetElementPtrInst(Value *to, Value *from, unsigned type)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        switch (type) {
            case 0:
                fact = "(rule (getElementPtr_base " + toString + ' ' + fromString + "))";
                return fact;
                break;
            case 1:
                fact = "(rule (getElementPtr_index " + toString + ' ' + fromString + "))";
                return fact;
                break;
            default:
                break;
        }
    }
    
    std::string genFact::createIntToPtrInst(Value *to, Value *from)
    {
        Instruction *to_inst = cast<Instruction>(to);
        Instruction *from_inst = cast<Instruction>(from);
        int to_num = IDMap[to_inst];
        int from_num = IDMap[from_inst];
        std::string toString = "#x" + ToBitVecForm(to_num, input_s);
        std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
        std::string fact;
        fact = "(rule (intToPtr " + toString + ' ' + fromString + "))";
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
            std::string toString = "#x" + ToBitVecForm(to_num, input_s);
            std::string fromString = "#x" + ToBitVecForm(from_num, input_s);
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
                }else if ((!opName.compare("and")) || (!opName.compare("or")))
                {
                    return createAndOr(toString, fromString, OP_ID);
                }
                else {
                    return createAssign(toString, fromString);
                }
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
            unsigned from1_num = IDMap[from1_inst];
            unsigned from2_num = IDMap[from2_inst];
            std::string from1String = "#x" + ToBitVecForm(from1_num, input_s);
            std::string from2String = "#x" + ToBitVecForm(from2_num, input_s);
            std::string fact;
            fact = "(rule (store_assign " + from1String + ' ' + from2String + "))";
            return fact;
        }
        Value *type_v;
        std::string fromString; // the number %XXX
        unsigned from_num;
        std::string store_name;
        if(!isa<Instruction>(from1))
        {
            type_v = from1;
            if(isa<Instruction>(from2))
            {
                Instruction *from_inst = dyn_cast<Instruction>(from2);
                from_num = IDMap[from_inst];
                fromString = "#x" + ToBitVecForm(from_num, input_s);
            }
            if(from1->hasName())
                store_name = from1->getName().str();
                
        }
        else //(!isa<Instruction>(from2))
        {
            type_v = from2;
            if(isa<Instruction>(from1))
            {
                Instruction *from_inst = dyn_cast<Instruction>(from1);
                from_num = IDMap[from_inst];
                fromString = "#x" + ToBitVecForm(from_num, input_s);
            }
            if(from2->hasName())
                store_name = from2->getName().str();
        }
        std::string fact;
        fact = ";(store_assign " + fromString + ' ' + store_name + ")";
        return fact;
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
