/*** generate the facts of the IR ***/
/*** output in the SMT-LIB2 form ***/
/*** author: Jingbo Wang ***/

#include "genFact.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include <string>
#include <iostream>
#include <sstream>
#include <bitset>
#include <algorithm>
#include <math.h>
#include <vector>

namespace assign{
    genFact::genFact(raw_fd_ostream *os, std::map<Instruction*, int> IDMap, std::vector<std::string> RAND_VAR, std::vector<std::string> CONSTANT_VAR, std::vector<std::string> KEY_VARi, unsigned input_s, unsigned input_ind, unsigned input_bitset)
    {
        this->datalogFiles = os;
        this->IDMap = IDMap;
        this->RAND_VAR = RAND_VAR;
        this->CONSTANT_VAR = CONSTANT_VAR;
        this->KEY_VAR = KEY_VAR;
        this->input_s = input_s;
        this->input_ind = input_ind;
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
        if(isa<Instruction>(op1))
        {
            fact1 = createBinaryOp(&I, op1, "left");
            writeFact(&I, fact1);
        }
        /** IF op1 is not instr, it may be constant or name, which we ignore **/
        if(isa<Instruction>(op2))
        {
            fact2 = createBinaryOp(&I, op2, "right");
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
        fact = createStore(val, ptr);
        writeFact(&I, fact);
    }

    std::string genFact::createLoad(Value *to, Value *from)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        assert(from->getType() && "from value with NULL type");
        assert(from->getType()->isPointerTy() && "from value that is not a pointer");
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            Instruction *from_inst = cast<Instruction>(from);
            int to_num = IDMap[to_inst];
            int from_num = IDMap[from_inst];
            std::string toString = "#b" + ToBitVecForm(to_num, input_s);
            std::string fromString = "#b" + ToBitVecForm(from_num, input_s);
            return createLoadAssign(toString, fromString);
        } else
        {
            errs() << "[ERROR] the operand of LoadInst is not instruction" << '\n';
        }
    }

    std::string genFact::createBinaryOp(Value *to, Value *from, std::string OP_ID)
    {
        assert(to && "to : NULL passed");
        assert(from && "from : NULL passed");
        if((isa<Instruction>(to)) && (isa<Instruction>(from)))
        {
            Instruction *to_inst = cast<Instruction>(to);
            int to_num = IDMap[to_inst];
            std::string toString = "#b" + ToBitVecForm(to_num, input_s);
            Instruction *from_inst = cast<Instruction>(from);
            int from_num = IDMap[from_inst];
            std::string fromString = "#b" + ToBitVecForm(from_num, input_s); 
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
        } else {
            errs() << "[ERROR] the operand of binary op is not Instruction" << '\n';
        }
    }

    /** for store inst, the fact is directly written in the datalog file **/
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
            std::string from1String = "#b" + ToBitVecForm(from1_num, input_s);
            std::string from2String = "#b" + ToBitVecForm(from2_num, input_s);
            return createStoreAssign(from2String, from1String);
        }
        Value *type_v;
        std::string fromString;
        if(!isa<Instruction>(from1))
        {
            type_v = from1;
            Instruction *from2_inst = cast<Instruction>(from2);
            int from2_num = IDMap[from2_inst];
            fromString = "#b" + ToBitVecForm(from2_num, input_s);
        }
        else //(!isa<Instruction>(from2))
        {
            type_v = from2;
            Instruction *from1_inst = cast<Instruction>(from1);
            int from1_num = IDMap[from1_inst];
            fromString = "#b" + ToBitVecForm(from1_num, input_s);
        }

        std::string fact;
        std::string var_name;
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
                unsigned iter_r = (rand_var_id_n) % 4;
                iter_r = 1 << (iter_r);
                for(unsigned j = 0; j < input_ind; j++)
                {
                    std::string index = "#b" + ToBitVecForm((1 << j), input_ind);
                    if(j == (rand_var_id_n/4))
                    {
                        std::string rand_var = "#b" + ToBitVecForm(iter_r, input_bitset);
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n"; 
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n"; 
                    }else
                    {
                        std::string rand_var = "#b" + ToBitVecForm(0, input_bitset);
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + rand_var + "))" + "\n";
                    }
                }
                return fact;
            }else if(std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) != CONSTANT_VAR.end())
            {
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (CONSTANT" + ' ' + fromString + "))" + "\n";
                unsigned cons_var_id_n = std::find(CONSTANT_VAR.begin(), CONSTANT_VAR.end(), var_name) - CONSTANT_VAR.begin();
                cons_var_id_n = cons_var_id_n + r_s + k_s;
                unsigned iter_r = cons_var_id_n % 4;
                iter_r = 1 << (iter_r);
                for(unsigned j = 0; j < input_ind; j++)
                {
                    std::string index = "#b" + ToBitVecForm((1 << j), input_ind);
                    std::string zero_s = "#b" + ToBitVecForm(0, input_bitset);
                    if(j == (cons_var_id_n/4))
                    {
                        std::string cons_var = "#b" + ToBitVecForm(iter_r, input_bitset);
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + cons_var + ' ' + "))" + "\n";
                    }else
                    {
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    }
                }
                return fact;
            }else{ 
                /** belongs to the key set **/
                fact = ';' + var_name + "==>" + ' ' + "type" + "\n";
                fact = fact + "(rule (KEY_SENSITIVE" + ' ' + fromString + "))" + "\n";
                unsigned key_var_id_n = std::find(KEY_VAR.begin(), KEY_VAR.end(), var_name) - KEY_VAR.begin();
                key_var_id_n = key_var_id_n + r_s;
                unsigned iter_r = key_var_id_n % 4;
                iter_r = 1 << iter_r;
                for(unsigned j = 0; j < input_ind; j++)
                {
                    std::string index = "#b" + ToBitVecForm((1 << j), input_ind);
                    std::string zero_s = "#b" + ToBitVecForm(0, input_bitset);
                    if(j == (key_var_id_n/4))
                    {
                        std::string key_var = "#b" + ToBitVecForm(iter_r, input_bitset);
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + key_var + ' ' + "))" + "\n";
                    }else
                    {
                        fact = fact + "(rule (REC_RAND_VAR" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                        fact = fact + "(rule (REC_ALL_INC" + ' ' + fromString + ' ' + index + ' ' + zero_s + ' ' + "))" + "\n";
                    }
                }
                /** intial convert version **/
                //std::string key_var = "#b" + std::bitset<input_s>(key_var_id).to_string();
            }
            return fact;
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
