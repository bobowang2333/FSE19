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
    genFact::genFact(raw_fd_ostream *os, std::map<Instruction*, int> &IDMap, std::vector<std::string> RAND_VAR, std::vector<std::string> CONSTANT_VAR, std::vector<std::string> KEY_VAR, unsigned input_s, unsigned input_ind, unsigned input_num,unsigned input_bitset, std::map<Instruction*, std::vector<unsigned>> REC_ALL_INC, std::map<Instruction*, std::vector<unsigned>> REC_RAND_VAR)
    {
        this->datalogFiles = os;
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
        std::string fact, ret;
        if(isa<Instruction>(ptr))
        {
            fact = createLoad(&I, I.getPointerOperand());
            writeFact(&I, fact);
            ret = preCal_load(&I, I.getPointerOperand());
            writeFact(&I, ret);
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
        std::string REC;
        if((isa<Instruction>(op1)) && (isa<Instruction>(op2)))
        {
            fact1 = createBinaryOp(&I, op1, "left");
            writeFact(&I, fact1);
            fact2 = createBinaryOp(&I, op2, "right");
            writeFact(&I, fact2);
            REC = preCal_binary(&I, op1, op2);
            writeFact(&I, REC);
        }
        /** IF op1 is not instr, it may be constant or name, which we use load_assign to represent the xor, and or op with constant operands **/
        else if((isa<Instruction>(op1)) && (!(isa<Instruction>(op2))))
        {
            fact1 = createBinaryConstant(&I, op1);
            writeFact(&I, fact1);
            REC = preCal_load(&I, op1);
            writeFact(&I, REC);
        }else if((isa<Instruction>(op2)) && (!(isa<Instruction>(op1))))
        {
            fact2 = createBinaryConstant(&I, op2);
            writeFact(&I, fact2);
            REC = preCal_load(&I, op2);
            writeFact(&I, REC);
        }
    }

    void genFact::visitStoreInst(StoreInst &I)
    {
        Value *val = I.getValueOperand();
        assert(val->getType() != NULL && "NULL Type being stored");
        Value *ptr = I.getPointerOperand();
        std::string fact, ret;
        /** only both value and pointer are both instr, then we build this relation **/
        fact = createStore(ptr, val);
        if(fact.size())
        {
            writeFact(&I, fact);
            if(isa<Instruction>(ptr) && isa<Instruction>(val))
            {
                ret = preCal_load(ptr, val);
                writeFact(&I, ret);
            }
        }
    }
    
    void genFact::visitTruncInst(TruncInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact, ret;
        fact = createTrunc(&I, op1);
        writeFact(&I, fact);
        ret = preCal_load(&I, op1);
        writeFact(&I, ret);
    }
    
    void genFact::visitZExtInst(ZExtInst &I)
    {
        Value *op1 = I.getOperand(0);
        std::string fact, ret;
        fact = createZExtInst(&I, op1);
        writeFact(&I, fact);
        ret = preCal_load(&I, op1);
        writeFact(&I, ret);
    }
    
    void genFact::visitICmpInst(ICmpInst &I)
    {
        /* for the imcp instruction: first op: type, second op: value1 third op: value2 */
        Instruction *inst = &I;
        User::op_iterator op_it;
        std::string fact, ret;
        for(op_it = inst->op_begin(); op_it != inst->op_end(); op_it++)
        {
            Use *u = &*op_it;
            Value *v = u->get();
            if(isa<Instruction>(u))
            {
                fact = createICmpInst(&I, v);
                writeFact(&I, fact);
                ret = preCal_load(&I, v);
                writeFact(&I, ret);
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
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            std::vector<unsigned> to_all, to_rand;
            if(REC_ALL_INC.find(from_inst) != REC_ALL_INC.end())
            {
                to_all = (REC_ALL_INC.find(from_inst))->second;
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, to_all));
                ret = write(to_inst, to_all, 1);
            }else
                ret = writeZero(to_inst, 0);
            if(REC_RAND_VAR.find(from_inst) != REC_RAND_VAR.end())
            {
                to_rand = (REC_RAND_VAR.find(from_inst))->second;
                REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, to_rand));
                ret = ret + write(to_inst, to_rand, 0);
            }
            // if the loaded variable is not random type, then we don't print out the information
            else{
                ret = ret + writeZero(to_inst, 1);
            }
            return ret;
        }else{
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
    }
    
    // type 1 => all_rec, type 0 => rand_var
    std::string genFact::write(Instruction *inst, std::vector<unsigned> rand_var, unsigned type)
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
        for(std::vector<unsigned>::iterator it = rand_var.begin(); it != rand_var.end(); it++)
        {
            res = res | (1 << (*it));
        }
        
        for(unsigned j = 1; j <= input_num; j++)
        {
            std::string index = "#b" + ToBitVecForm_original(j, input_ind);
            unsigned full = (1 << input_bitset) - 1;
            unsigned rand_time = (res >> ((j - 1) * input_bitset)) & full;
            std::string rand_var = "#b" + ToBitVecForm_original(rand_time, input_bitset);
            if(j == 1)
                ret = type_prefix + ' ' + instString + ' ' + index + ' ' + rand_var + "))" + "\n";
            else
                ret = ret + type_prefix + ' ' + instString + ' ' + index + ' ' + rand_var + "))" + "\n";
        }
        return ret;
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
                REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(to_inst, res_rand));
            }
            //else => the res_rand is empty Cz both operands are not rand
        }
        
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
    }
    
    std::vector<unsigned> genFact::SetOr(std::vector<unsigned> a, std::vector<unsigned> b)
    {
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
        return res;
    }
    
    std::vector<unsigned> genFact::XOR_ALL_INC(std::vector<unsigned> all_1, std::vector<unsigned> all_2, std::vector<unsigned> rand_1, std::vector<unsigned> rand_2)
    {
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
    }
    
    std::vector<unsigned> genFact::XOR_RAND_VAR(std::vector<unsigned> rand_1, std::vector<unsigned> rand_2)
    {
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
                unsigned rand_var_id_n = std::find(RAND_VAR.begin(), RAND_VAR.end(), var_name) - RAND_VAR.begin();
                //unsigned iter_r = (rand_var_id_n) % 4;
                unsigned iter_r = 1 << (rand_var_id_n);
                for(unsigned j = 1; j <= input_num; j++)
                {
                    std::string index = "#b" + ToBitVecForm_original(j, input_ind);
                    unsigned full = (1 << input_bitset) - 1;
                    unsigned rand_time = (iter_r >> ((j - 1) * input_bitset)) & full;
                    std::string rand_var = "#b" + ToBitVecForm_original(rand_time, input_bitset);
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                }
                integter_ind.push_back(rand_var_id_n);
                REC_RAND_VAR.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
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
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + cons_var + ' ' + "))" + "\n";
                }
                integter_ind.push_back(cons_var_id_n);
                REC_ALL_INC.insert(std::pair<Instruction*, std::vector<unsigned>>(inst_real, integter_ind));
                return fact;
            }else{ 
                /** belongs to the key set **/
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (KEY_SENSITIVE" + ' ' + fromString + "))" + "\n";
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
                    fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + key_var + ' ' + "))" + "\n";
                }
                integter_ind.push_back(key_var_id_n);
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
        (*datalogFiles) << getCommentMark() << ' ' << *v << '\n' << fact << '\n';
    }

    char genFact::getCommentMark() 
    {
        return ';';
    }
}
