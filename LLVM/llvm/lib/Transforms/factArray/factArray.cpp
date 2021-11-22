/*** simple assignment facts generation ***/
/*** output: z3 fix-point datalog file ***/
/*** author: Jingbo Wang ***/

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "genFact.h"
#include "math.h"
#include <string>
/** for reading the input specified file **/
#include <vector>
#include <sstream>
#include <iostream>
#include <fstream>
#include <string>
#include <iomanip>
#include <tuple>

using namespace llvm;
typedef std::tuple<std::string, std::string, std::string, std::string> share_pair;
typedef std::tuple<unsigned, Value*> arr_ind;
typedef std::tuple<unsigned, unsigned, unsigned> var_arr_value;
// #define ASSIGNMENT_DEBUG

/** add additional commands for user input to specify the type **/
cl::opt<std::string> InputFileName("input", cl::desc("specify the type file"), cl::value_desc("fileName"), cl::Required);
cl::opt<std::string> ShareFileName("share", cl::desc("specify the shared_variable file"), cl::value_desc("fileName"), cl::Required);

    struct factArray : public FunctionPass {
        static char ID;
        factArray() : FunctionPass(ID) {}

        std::vector<std::string> split (std::string input_s)
        {
            std::string buf;
            std::stringstream ss(input_s);
            std::vector<std::string> tokens;
            while(ss >> buf)
                tokens.push_back(buf);
            return tokens;
        }

        std::vector<std::string> InFileTypeSet (std::string type, std::string file_name)
        {
            std::string line;
            std::vector<std::string> s_vec;
            std::vector<std::string> type_output;
            std::ifstream input_file(file_name);
            if(input_file.is_open())
            {
                while(getline(input_file, line))
                {
                    s_vec = split(line);
                    if(!type.compare(s_vec[0]))
                    {
                        type_output.push_back(s_vec[1]);
                    }else
                        continue;
                }
            }
            input_file.close();
            return type_output;
        }

        std::string create_zero(unsigned input_s)
        {
            std::string ret;
            unsigned iter = 0;
            while(iter != input_s)
            {
                ret += '0';
                iter++;
            }
            ret = "#b" + ret;
            return ret;
        }
        
        //to bit string
        std::string ToBitVecForm_original (unsigned in, unsigned max_len)
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
        std::string ToBitVecForm(unsigned in, unsigned max_len)
        {
            if(max_len == 0)
            {
                std::string ERROR = ";the given length is less than the input value";
                return ERROR;
            }else{
                std::stringstream stream;
                stream << std::setfill('0') << std::setw(max_len/4) << std::hex << in;
                return stream.str();
            }
        }
        
        unsigned calExponent(unsigned input)
        {
            unsigned base = 2;
            unsigned tmp = 0;
            unsigned exp = 1;
            while(exp <= input)
            {
                exp *= base;
                tmp++;
            }
            return tmp;
        }
        
        /* use the backend information, to get the variable pair which shares the same register */
        void Share(raw_fd_ostream &f, unsigned input_s, Function &F, std::string share_file, std::map<Instruction*, int> ID_map)
        {
            static int cnt = 1;
            if(cnt < 2)
            {
                // the first individual function comes in, then it stops generating share information.
                cnt++;
                return;
            }
            std::map<std::string, std::string> alloca_var_id;
            std::map<int, share_pair> share_map;
            /*iterate Alloca inst and print the name of the instr and the corresponding ID */
            for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
            {
                Instruction *inst = &*i;
                const char *opcode_name = inst->getOpcodeName();
                std::string opcode_str(opcode_name);
                if(opcode_str.compare("alloca")){
                    if(!opcode_str.compare("getelementptr")){
                        //use "getelementptr" instr to indicate the %arrayidx40.i
                        int num = ID_map[inst];
                        std::stringstream stream;
                        stream << "#x" << std::setfill('0') << std::setw(input_s/4) << std::hex << num;
                        std::string instr_id = stream.str();
                        stream.str("");
                        if(inst->hasName())
                        {
                            std::string var_name = inst->getName().str();
                            alloca_var_id.insert(std::pair<std::string, std::string>(var_name, instr_id));
                        }
                    }else
                        continue;
                }
                else
                {
                    int num = ID_map[inst];
                    std::stringstream stream;
                    stream << "#x" << std::setfill('0') << std::setw(input_s/4) << std::hex << num;
                    std::string instr_id = stream.str();
                    stream.str("");
                    if(inst->hasName())
                    {
                        std::string var_name = inst->getName().str();
                        alloca_var_id.insert(std::pair<std::string, std::string>(var_name, instr_id));
                    }
                    
                }
            }

            /* read the "share_variable.txt" file to gain info */
            f << ";begin to print the share relation such as share(2) and share(3)\n";
            std::ifstream fin(share_file);
            std::string s;
            unsigned tmp = 0;
            while(getline(fin, s))
            {
                std::istringstream iss(s);
                std::vector<std::string> tokens;
                std::copy(std::istream_iterator<std::string>(iss), std::istream_iterator<std::string>(), std::back_inserter(tokens));
                iss.str("");
                iss.clear();
                if(tokens.size() == 1)
                    continue;
                else{
                    for(std::vector<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++)
                    {
                        if(!(*it).compare("share(2)"))
                        {
                            // two elements in share (one xor)
                            std::vector<std::string>::iterator it_after;
                            it_after = it;
                            ++it_after;
                            std::string share_s1, share_s2;
                            f << "; share_register_variable_pair: " << (*it_after) << " ";
                            share_s1 = alloca_var_id[(*it_after).substr(1, -1)];
                            ++it_after;
                            f << (*it_after) << "\n";
                            share_s2 = alloca_var_id[(*it_after).substr(1, -1)];
                            std::string fact;
                            fact = "(rule (share_2 " + share_s1 + " " + share_s2 + "))" + "\n";
                            f << fact;
                        }else if (!(*it).compare("share(3)"))
                        {
                            std::vector<std::string>::iterator it_after;
                            it_after = it;
                            ++it_after;
                            std::string share_s1, share_s2, share_s3;
                            share_s1 = alloca_var_id[(*it_after).substr(1, -1)];
                            f << "; share_register_variable_pair: " << (*it_after) << " ";
                            ++it_after;
                            share_s2 = alloca_var_id[(*it_after).substr(1, -1)];
                            f << (*it_after) << " ";
                            ++it_after;
                            share_s3 = alloca_var_id[(*it_after).substr(1, -1)];
                            f << (*it_after) << "\n";
                            std::string fact;
                            fact = "(rule (share_3 " + share_s1 + " " + share_s2 + " " + share_s3 + "))\n";
                            f << fact;
                        }else{
                            break;
                        }
                    }
                        
                }
            }
            f << "\n";
            fin.close();
        }
        

        inst_iterator getInstrIterator(Instruction *inst, Function &F)
        {
            inst_iterator i;
            for(i = inst_begin(F); i != inst_end(F); ++i)
            {
                Instruction *inst_iter = &*i;
                if(inst == inst_iter)
                {
                    return i;
                    break;
                }
            }
            return i;
        }
        
        bool isAfterCall(Function &F, inst_iterator it)
        {
            Instruction *inst = &*it;
            std::string inst_str = std::string(inst->getOpcodeName());
            if (!(inst_str.compare("call"))) {
                return true;
            }else{
                while (!(inst_str.compare("store"))) {
                    --it;
                    inst = &*it;
                    inst_str = std::string(inst->getOpcodeName());
                }
                if (!(inst_str.compare("call"))) {
                    return true;
                }else
                    return false;
            }
        }
        
        /* document the type of the elements in an array and return the width of the "Times" */
        unsigned assign_num(Function &F, raw_fd_ostream &f, std::map<Instruction*, int> id_map, std::vector<std::string> RAND, std::vector<std::string> CONSTANT, std::vector<std::string> KEY, unsigned input_s, unsigned input_bitset)
        {
            unsigned tmp1 = 0; //used for counting the elements in the same type
            std::map<unsigned, unsigned> callee_caller;
            std::map<arr_ind, unsigned> array_index;
            std::map<arr_ind, unsigned>::iterator it;
            std::vector<var_arr_value> Var_Arr_Value;
            for(inst_iterator i = inst_begin(F); i != inst_end(F); ++i)
            {
                Instruction *inst = &*i;
                const char *opcode_name = inst->getOpcodeName();
                std::string opcode_str = std::string(opcode_name);
                /*if the instr before store is "call", then it must be the transfer between caller parameters to callee parameters, which should be same */
                if(!opcode_str.compare("store"))
                {
                    inst_iterator i_before = i;
                    --i_before;
                    //last instr should be the "call"
                    //if(!(std::string(i_before->getOpcodeName()).compare("call")))
                    if(isAfterCall(F, i_before))
                    {
                        Value *from = inst->getOperand(0);
                        Value *to = inst->getOperand(1);
                        if(isa<Instruction>(from))
                        {
                            Instruction *from_inst  = dyn_cast<Instruction>(from);
                            inst_iterator store2 = getInstrIterator(from_inst, F);
                            while((std::string((&*store2)->getOpcodeName())).compare("getelementptr"))
                            {
                                store2--;
                            }
                            // for two continuously getelementptr instr ////////
                            inst_iterator store2_i = store2;
                            --store2_i;
                            if((std::string((&*store2_i)->getOpcodeName())).compare("load"))
                            {
                                store2 = store2_i;
                            }
                            //////////////////////
                            Value *array_base = (&*store2)->getOperand(0);
                            Instruction *array_base_inst = dyn_cast<Instruction>(array_base);
                            inst_iterator store3 = getInstrIterator(array_base_inst, F);
                            // this should be a load instr: array_base: load %initial
                            Value *initial = (&*store3)->getOperand(0);
                            Instruction *to_inst = dyn_cast<Instruction>(to);
                            Instruction *initial_inst = dyn_cast<Instruction>(initial);
                            unsigned callee = id_map[to_inst];
                            unsigned caller = id_map[initial_inst];
                            callee_caller.insert(std::pair<unsigned, unsigned>(callee, caller));
                            // put the (%22, %22) pair in; which is the (caller, caller) pair
                            if(callee_caller.find(caller) != callee_caller.end())
                                continue;
                            else
                                callee_caller.insert(std::pair<unsigned, unsigned>(caller, caller));
                        }
                    }
                    
                }
            }
            
            // decide the rand number for those special variables
            for(inst_iterator i = inst_begin(F); i != inst_end(F); ++i)
            {
                Instruction *inst = &*i;
                const char *opcode_name = inst->getOpcodeName();
                std::string opcode_str = std::string(opcode_name);
                /*for "getelementptr" instr: if the next instrs don't have the inttoptr or store instr, then it must access the elements in an array*/
                if(!(opcode_str.compare("getelementptr"))){
                    inst_iterator getele1 = i;
                    inst_iterator getele_before = i;
                    --getele_before;
                    getele1++;
                    // (No Store)
                    Instruction *inst_next = &*getele1;
                    std::string opcode_str_next = std::string(inst_next->getOpcodeName());
                    if(opcode_str_next.compare("store"))
                    {
                        //////for two continuously getelementptr
                        //getele1++;
                        //getele1++;
                        // (No inttoptr) wait to see if there is the inttoptr instr
                        //if((std::string((&*getele1)->getOpcodeName())).compare("inttoptr"))
                        if(((std::string((&*getele1)->getOpcodeName())).compare("getelementptr")) && ((std::string((&*getele_before)->getOpcodeName())).compare("getelementptr")))
                        {
                            // analyze the "getelementptr" instr
                            inst_iterator getBase = i;
                            unsigned op_value = id_map[inst];
                            // the "load" instr before the "getelementptr" instr
                            getBase--;
                            Value *arr_base = (&*getBase)->getOperand(0);
                            Instruction *arr_base_inst = dyn_cast<Instruction>(arr_base);
                            Value *index = (&*i)->getOperand(1);
                            if(isa<Instruction>(arr_base))
                            {
                                unsigned base_ind = id_map[arr_base_inst];
                                if(callee_caller.empty())
                                    continue;
                                unsigned original_base_ind = callee_caller[base_ind];
                                it = array_index.find(std::make_tuple(original_base_ind, index));
                                if(it != array_index.end())
                                {
                                    // write the existing tmp to the Var_Arr_Value array
                                    unsigned tmp = it->second;
                                    Var_Arr_Value.push_back(std::make_tuple(op_value, original_base_ind, tmp));
                                }else
                                {
                                    // add the new(base+ind) combination and write the fact to file
                                    tmp1++; //the type variable starts from #b0001
                                    array_index.insert(std::pair<arr_ind, unsigned>(std::make_tuple(original_base_ind, index), tmp1));
                                    Var_Arr_Value.push_back(std::make_tuple(op_value, original_base_ind, tmp1));
                                }
                            }
                        }
                    }
                    
                }
                
            }
            // the total number of the typed variables
            unsigned ss;
            // all the bits needed to represent the type input variables
            ss = array_index.size();
            // return the bit width of the "times"
            unsigned index_num = (ss%4)?((ss/4)+1):(ss/4);
            unsigned index = calExponent(index_num+1);
            printSort(f, input_s, input_bitset, index);
            // based on RAND_VAR KET_VAR CONSTANT_VAR, fill in the datalog facts
            for(inst_iterator i = inst_begin(F); i != inst_end(F); ++i)
            {
                Instruction *inst = &*i;
                const char *opcode_name = inst->getOpcodeName();
                std::string opcode_str = std::string(opcode_name);
                if(!opcode_str.compare("store"))
                {
                    Value *op1 = inst->getOperand(0);
                    if(!isa<Instruction>(op1))
                    {
                        if(op1->hasName())
                        {
                            std::string operand_str = op1->getName().str();
                            if(find(RAND.begin(), RAND.end(), operand_str) != RAND.end())
                            {
                                Value *arr_base = inst->getOperand(1);
                                Instruction *arr_base_inst = dyn_cast<Instruction>(arr_base);
                                unsigned arr_base_id = id_map[arr_base_inst];
                            // fill the form(RAND_VAR var times bitset)
                                unsigned type = 1; //for rand
                                mark_type(f, arr_base_id, Var_Arr_Value, type, input_s, input_bitset, ss, operand_str);
                            }else if (find(KEY.begin(), KEY.end(), operand_str) != KEY.end()) {
                                Value *arr_base = inst->getOperand(1);
                                Instruction *arr_base_inst = dyn_cast<Instruction>(arr_base);
                                unsigned arr_base_id = id_map[arr_base_inst];
                                unsigned type = 2; //for key
                                mark_type(f, arr_base_id, Var_Arr_Value, type, input_s, input_bitset, ss, operand_str);
                            }else if (find(CONSTANT.begin(), CONSTANT.end(), operand_str) != CONSTANT.end()){ // for the constant type
                                Value *arr_base = inst->getOperand(1);
                                Instruction *arr_base_inst = dyn_cast<Instruction>(arr_base);
                                unsigned arr_base_id = id_map[arr_base_inst];
                                unsigned type = 3; //for constant
                                mark_type(f, arr_base_id, Var_Arr_Value, type, input_s, input_bitset, ss, operand_str);
                            }else {
                                continue;
                            }
                        }
                    }
                }
            }
            return index;
        }
        
        void printSort(raw_fd_ostream &f, unsigned input_s, unsigned input_bitset, unsigned input_ind)
        {
            f << ";add sort and relation definition in advance\n"
              << "(define-sort s () (_ BitVec "
              << std::to_string(input_s)
              << "))\n"
              << "(define-sort BitSet () (_ BitVec "
              << std::to_string(input_bitset)
              << "))\n"
              << "(define-sort ind () (_ BitVec "
              << std::to_string(input_ind)
              << "))\n"
              << "; define the types which are gonna be used\n"
              << "(declare-rel KEY_SENSITIVE (s))\n"
              << "(declare-rel KEY_IND (s))\n"
              << "(declare-rel CONSTANT (s))\n"
              << "(declare-rel RAND (s))\n"
              << "(declare-rel HD_SENSITIVE (s s))\n"
              << "\n"
              << "; define the TYPE array\n"
              << "(declare-rel RAND_NUMBER (ind BitSet))\n"
              << "(declare-rel KEY_NUMBER (ind BitSet))\n"
              << "(declare-rel REC_RAND_VAR (s ind BitSet))\n"
              << "(declare-rel REC_ALL_INC (s ind BitSet))\n"
              << "(declare-rel Time (ind))\n"
              << "\n";
        }
        
        // type 0-> rand; 1-> key; 2-> constant
        // s-> tmp1, the sum of all the type varibles
        void mark_type(raw_fd_ostream &f, unsigned arr_base, std::vector<var_arr_value> mark_arr, unsigned type, unsigned input_s, unsigned input_bitset, unsigned ss, std::string base_str)
        {
            // the sum of how many variables in a specific type
            std::vector<unsigned> ss_type;
            unsigned index_num = (ss%4)?((ss/4)+1):(ss/4);
            unsigned index = calExponent(index_num+1); // times starts from 1 instead of 0
            std::string time = "#b" + ToBitVecForm_original(index_num, index);
            time = "(rule (Time " + time + "))" + "\n";
            f << time;
            for(std::vector<var_arr_value>::iterator it = mark_arr.begin(); it != mark_arr.end(); ++it)
            {
                // 0-> op_value, 1-> array_base, 2-> assigned random value/key value
                unsigned tuple_base = std::get<1>(*it);
                if(!(arr_base == tuple_base))
                    continue;
                else{
                    unsigned op_value = std::get<0>(*it);
                    unsigned tmp_value = std::get<2>(*it);
                    //sum_number += (1 << tmp_value);
                    // dividing by 4: cz the size of bitset is 4
                    unsigned times_ind = (tmp_value%4)?((tmp_value/4) + 1):(tmp_value/4); // times
                    unsigned times_value = (tmp_value - 1)%4; // 4-bit bitset
                    switch (type) {
                        case 1: //rand
                            printType(f, base_str, op_value, 1, times_ind, times_value, index, index_num, input_s, input_bitset);
                            ss_type.push_back(tmp_value);
                            break;
                        case 2: //key
                            printType(f, base_str, op_value, 2, times_ind, times_value, index, index_num, input_s, input_bitset);
                            ss_type.push_back(tmp_value);
                            break;
                        default: //constant
                            printType(f, base_str, op_value, 3, times_ind, times_value, index, index_num, input_s, input_bitset);
                            ss_type.push_back(tmp_value);
                            break;
                    }
                }
            }
            // print the number "(RAND_NUMBER )"
            printSS(f, ss_type, type, index_num, index, input_bitset);
        }
        
        /* input_ind: the bit width of times; input_times: the value of times */
        void printType(raw_fd_ostream &f, std::string op_name, unsigned op_value, unsigned type, unsigned times_ind, unsigned times_value, unsigned input_ind, unsigned input_times, unsigned input_s, unsigned input_bitset)
        {
            std::string var_str = "#x" + ToBitVecForm(op_value, input_s);
            std::string one_bitset = "#x" + ToBitVecForm((1 << times_value), input_bitset);
            std::string zero_bitset = "#x" + ToBitVecForm(0, input_bitset);
            std::string fact;
            // write the type of the variables to file
            switch (type) {
                case 1: //rand
                    fact = ';' + op_name + "==>" + ' ' + "type" + "\n";
                    fact = fact + "(rule (RAND " + ' ' + var_str + "))" + "\n";
                    f << fact;
                    break;
                case 2: //key
                    fact = ';' + op_name + "==>" + ' ' + "type" + "\n";
                    fact = fact + "(rule (KEY_SENSITIVE " + ' ' + var_str + "))" + "\n";
                    f << fact;
                    break;
                default:
                    fact = ';' + op_name + "==>" + ' ' + "type" + "\n";
                    fact = fact + "(rule (CONSTANT " + ' ' + var_str + "))" + "\n";
                    f << fact;
                    break;
            }
            // write the rand var list and others to the file
            for(unsigned i = 1; i <= input_times; ++i)
            {
                std::string id = "#b" + ToBitVecForm_original(i, input_ind);
                if(i == times_ind)
                {
                    if(type == 1)
                        fact = "(rule (REC_RAND_VAR " + var_str + ' ' + id + ' ' + one_bitset + " ))" + "\n";
                    else
                        fact = "(rule (REC_RAND_VAR " + var_str + ' ' + id + ' ' + zero_bitset + " ))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC " + var_str + ' ' + id + ' ' + one_bitset + " ))" + "\n";
                    f << fact;
                }else{
                    fact = "(rule (REC_RAND_VAR " + var_str + ' ' + id + ' ' + zero_bitset + ' ' + "))" + "\n";
                    fact = fact + "(rule (REC_ALL_INC " + var_str + ' ' + id + ' ' + zero_bitset + ' ' + "))" + "\n";
                    f << fact;
                }
            }
        }
        
        // print the sum number of each type
        void printSS(raw_fd_ostream &f, std::vector<unsigned> ss, unsigned type, unsigned index_num, unsigned input_ind, unsigned input_bitset)
        {
            std::string type_str;
            switch (type) {
                case 1:
                    type_str = "RAND_NUMBER";
                    break;
                case 2:
                    type_str = "KEY_NUMBER";
                    break;
                default:
                    return;
                    break;
            }
            // there are index_num rounds
            for(unsigned i = 1; i <= index_num; ++i)
            {
                // for each round, check the value is in the range of bitset
                unsigned cnt = 0;
                for(unsigned j = input_bitset*(i-1); j < input_bitset*i; ++j)
                {
                    if(find(ss.begin(), ss.end(), j) != ss.end())
                    {
                        unsigned j_bitset = (j%4);
                        cnt += (1 << j_bitset);
                    }
                }
                // print each round
                std::string id = "#b" + ToBitVecForm_original(i, input_ind);
                std::string type_s = "#x" + ToBitVecForm(cnt, input_bitset);
                std::string type_num = "(rule (" + type_str + ' ' + id + ' ' + type_s + "))" + "\n";
                f << type_num;
            }
        }
        
        void printSpec(raw_fd_ostream &f, unsigned input_s, unsigned input_ind, unsigned input_bitset) {
            //Using SMT-LIB
            std::string unsigned_size_bits = std::to_string(sizeof(unsigned) * 2);
            f << "(set-option :fixedpoint.engine datalog)\n"
              << "; this sort is used to define all the relations\n"
              << "\n";
            f << "; assignment (assign from to)\n"
              << "(declare-rel assign(s s))\n"
              << "(declare-rel TDEP (s s))\n"
              << "(declare-rel xor_assign_left (s s))\n"
              << "(declare-rel xor_assign_right (s s))\n"
              << "(declare-rel andor_assign_left (s s))\n"
              << "(declare-rel andor_assign_right (s s))\n"
              << "(declare-rel not_assign (s s))\n"
              << "(declare-rel load_assign (s s))\n"
              << "(declare-rel store_assign (s s))\n"
              << "(declare-rel zext_assign (s s))\n"
              << "(declare-rel icmp_assign (s s))\n"
              << "(declare-rel trunc_assign (s s))\n"
              << "(declare-rel share_2 (s s))\n"
              << "(declare-rel share_3 (s s s))\n"
              << "(declare-rel binary_constant(s s))\n"
              << "(declare-rel equal_assign (s s))\n"
              << "; add after the factArray\n"
              << "(declare-rel sext_assign (s s))\n"
              << "(declare-rel getElementPtr_base (s s))\n"
              << "(declare-rel getElementPtr_index (s s))\n"
              << "\n"
              << "; declare varibles which are used to define the rules (type:s)\n"
              << "(declare-var var s)\n"
              << "(declare-var prev s)\n"
              << "(declare-var to s)\n"
              << "(declare-var from s)\n"
              << "(declare-var from1 s)\n"
              << "(declare-var from2 s)\n"
              << "(declare-var to_e s)\n"
              << "(declare-var from_e s)\n"
              << "(declare-var from1_e s)\n"
              << "(declare-var from2_e s)\n"
              << "\n"
              << "; declare variables which are used (type: bitSet)\n"
              << "(declare-var RAND_A BitSet)\n"
              << "(declare-var RAND_B BitSet)\n"
              << "(declare-var RAND_C BitSet)\n"
              << "(declare-var ALL_INC_A BitSet)\n"
              << "(declare-var ALL_INC_B BitSet)\n"
              << "(declare-var ALL_INC_C BitSet)\n"
              << "(declare-var RAND_NUM BitSet)\n"
              << "(declare-var KEY_NUM BitSet)\n"
              << "(declare-var int_res0 BitSet)\n"
              << "(declare-var int_res1 BitSet)\n"
              << "(declare-var int_res2 BitSet)\n"
              << "(declare-var int_bool0 bool)\n"
              << "(declare-var int_bool1 bool)\n"
              << "\n";
            // define the DEP relation
        }

        void printRule(raw_fd_ostream &f, unsigned input_ind, unsigned input_bitset)
        {
            std::string zero_bit = create_zero(input_bitset);
            std::string zero_ind = create_zero(input_ind);
            std::string one_ind = "#b" + ToBitVecForm_original(1, input_ind);
            f << "; define the function which will be used in the rules\n"
              << "(declare-rel BVAND (BitSet BitSet BitSet))\n"
              << "(declare-rel BVOR (BitSet BitSet BitSet))\n"
              << "(declare-rel BVNOT (BitSet BitSet))\n"
              << "(declare-rel BV_Intersect (BitSet BitSet BitSet))\n"
              << "(declare-rel BV_Diff (BitSet BitSet BitSet))\n"
              << "(declare-rel ISEMPTY (BitSet bool))\n"
              << "(declare-rel NOEMPTY (BitSet bool))\n"
              << "(declare-rel SET_SUM (BitSet BitSet BitSet))\n"
              << "(declare-rel XOR_RUD1_ALL_INC (BitSet BitSet BitSet BitSet BitSet BitSet))\n"
              << "(declare-rel BV_EQUAL (BitSet BitSet))\n"
              << "(declare-rel BV_ZERO (BitSet BitSet))\n"
              << "\n"
              << "; define the recursive function used in the rules\n"
              << "(declare-rel BVAND_REC (s s s ind))\n"
              << "(declare-rel BVAND_ALL_KEY_REC (s ind BitSet))\n"
              << "(declare-rel BVOR_RAND_REC (s s s ind))\n"
              << "(declare-rel BVOR_ALL_REC (s s s ind))\n"
              << "(declare-rel BV_INTERSECT_REC (s s ind BitSet))\n"
              << "(declare-rel INTERSECT_LABEL (s s))\n"
              << "(declare-rel BV_DIFF_REC (s s ind BitSet))\n"
              << "(declare-rel DIFF_LABEL (s s))\n"
              << "(declare-rel BV_SAME_REC (s s ind BitSet))\n"
              << "(declare-rel CHECK_SAME (s s))\n"
              << "(declare-rel SET_SUM_REC (s s s ind))\n"
              << "(declare-rel XOR_RUD1_ALL_INC_REC (s s s ind))\n"
              << "(declare-rel BV_EQUAL_RAND_REC (s s ind))\n"
              << "(declare-rel BV_EQUAL_ALL_REC (s s ind))\n"
              << "(declare-rel BV_ZERO_REC (s s ind))\n"
              << "(declare-rel BV_IS_EMPTY_REC (s ind bool))\n"
              << "\n"
              << "; define the variables used for the function\n"
              << "(declare-var X BitSet)\n"
              << "(declare-var Y BitSet)\n"
              << "(declare-var Z BitSet)\n"
              << "(declare-var X_A BitSet)\n"
              << "(declare-var Y_A BitSet)\n"
              << "(declare-var X_R BitSet)\n"
              << "(declare-var Y_R BitSet)\n"
              << "(declare-var N BitSet)\n"
              << "(declare-var Times ind)\n"
              << "(declare-var Times_New ind)\n"
              << "(declare-var Times_Past ind)\n"
              << "(declare-var time ind)\n"
              << "(declare-var var_x s)\n"
              << "(declare-var var_y s)\n"
              << "(declare-var var_z s)\n"
              << "(declare-var X_T BitSet)\n"
              << "(declare-var Y_T BitSet)\n"
              << "(declare-var Z_T BitSet)\n"
              << "(declare-var XY BitSet)\n"
              << "(declare-var XY_past BitSet)\n"
              << "(declare-var tmp BitSet)\n"
              << "\n"
              << "; define the functions\n"
              << "(rule (=> (and true true) (BVAND X Y (bvand X Y))))\n"
              << "(rule (=> (and true true) (BVOR X Y (bvor X Y))))\n"
              << "(rule (=> (and true true) (BVNOT X (bvnot X))))\n"
              << "(rule (=> (and true true) (BV_Intersect X Y (bvand X Y))))\n"
              << "(rule (=> (and true true) (BV_Diff X Y (bvand X (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y))))))\n"
              << "(rule (=> (and true true) (ISEMPTY X (= X "
              << zero_bit
              << "))))\n"
              << "(rule (=> (and true true) (SET_SUM X Y (bvor (bvand X (bvnot Y)) (bvand (bvnot X) Y)))))\n"
              << "(rule (=> (and true true) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R N (bvand (bvor X_A Y_A) (bvor (bvnot N) (bvor (bvand X_R (bvnot Y_R)) (bvand (bvnot X_R) Y_R)))))))\n"
              << "(rule (=> (and true true) (BV_EQUAL X X)))\n"
              << "(rule (=> (and true true) (BV_ZERO X (bvand "
              << zero_bit
              << " X))))\n"
              << "\n";
            f << "; defining the recursive function ;;;;;;;\n"
              << ";; BV [AND] [RAND_VAR] ;; Times begin from 1 \n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVAND_REC var_x var_y var_z Times) (= tmp (bvand X Y))) (REC_RAND_VAR var_z Times tmp)))\n"
              << "(rule (=> (and (BVAND_REC var_x var_y var_z Times) (not (= Times "
              << zero_ind
              << ")) (= Times_New (bvsub Times "
              << one_ind
              << "))) (BVAND_REC var_x var_y var_z Times_New)))\n"
              << ";; BV [AND] = [KEY] && [ALL_INC] ;;; for the [NO KEY] rule ;;;;;;\n"
              << ";(rule (=> (and (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res0) (= Times "
              << one_ind
              << ")) (BVAND_ALL_KEY_REC var_x Times int_res0)))\n"
              << ";(rule (=> (and (BVAND_ALL_KEY_REC var_x Times_New int_res0) (REC_ALL_INC var_x Times X) (KEY_NUMBER Times KEY_NUM) (BVAND X KEY_NUM int_res1) (= Times_New (bvsub Times "
              << one_ind
              << ")) (not (= Times "
              << one_ind
              << ")) (BVOR int_res0 int_res1 int_res2)) (BVAND_ALL_KEY_REC var_x Times int_res2)))\n"
              << ";; BV [OR] [RAND_VAR]\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (BVOR_RAND_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_RAND_VAR var_z Times XY)))\n"
              << "(rule (=> (and (BVOR_RAND_REC var_x var_y var_z Times) (not (= Times "
              << zero_ind
              << ")) (= Times_New (bvsub Times "
              << one_ind
              << "))) (BVOR_RAND_REC var_x var_y var_z Times_New)))\n"
              << ";; BV [OR] [ALL_INC]\n"
              << "(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (BVOR_ALL_REC var_x var_y var_z Times) (BVOR X Y XY)) (REC_ALL_INC var_z Times XY)))\n"
              << "(rule (=> (and (BVOR_ALL_REC var_x var_y var_z Times) (not (= Times "
              << zero_ind
              << ")) (= Times_New (bvsub Times "
              << one_ind 
              << "))) (BVOR_ALL_REC var_x var_y var_z Times_New)))\n"
              << ";; BV [Intersect] [ALL_INC]\n"
              << "(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times "
              << one_ind
              << ") (BV_Intersect X Y XY)(INTERSECT_LABEL var_x var_y)) (BV_INTERSECT_REC var_x var_y Times XY)))\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times "
              << one_ind
              << ")) (BV_Intersect X Y XY) (INTERSECT_LABEL var_x var_y) (= Times_New (bvsub Times "
              << one_ind
              << ")) (BV_INTERSECT_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_INTERSECT_REC var_x var_y Times int_res0)))\n"
              << ";; BV [DIFF] [RAND_VAR]\[ALL_INC]\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (= Times "
              << one_ind
              << ") (BV_Diff X Y XY) (DIFF_LABEL var_x var_y)) (BV_DIFF_REC var_x var_y Times XY)))\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times "
              << one_ind
              << ")) (BV_Diff X Y XY) (DIFF_LABEL var_x var_y) (= Times_New (bvsub Times "
              << one_ind
              << ")) (BV_DIFF_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_DIFF_REC var_x var_y Times int_res0)))\n"
              << ";; BV [SAME] [ALL_INC] [ALL_INC]\n"
              << "(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (= Times "
              << one_ind
              << ") (SET_SUM X Y XY)(CHECK_SAME var_x var_y)) (BV_SAME_REC var_x var_y Times XY)))\n"
              << "(rule (=> (and (REC_ALL_INC var_x Times X) (REC_ALL_INC var_y Times Y) (not (= Times "
              << one_ind
              << ")) (SET_SUM X Y XY) (CHECK_SAME var_x var_y) (= Times_New (bvsub Times "
              << one_ind
              << ")) (BV_SAME_REC var_x var_y Times_New XY_past) (BVOR XY XY_past int_res0)) (BV_SAME_REC var_x var_y Times int_res0)))\n"
              << ";; BV [SET_SUM] [RAND_VAR] [RAND_VAR]\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (REC_RAND_VAR var_y Times Y) (SET_SUM_REC var_x var_y var_z Times) (SET_SUM X Y XY)) (REC_RAND_VAR var_z Times XY)))\n"
              << "(rule (=> (and (SET_SUM_REC var_x var_y var_z Times) (not (= Times_New "
              << zero_ind
              << ")) (= Times_New (bvsub Times "
              << one_ind
              << "))) (SET_SUM_REC var_x var_y var_z Times_New)))\n"
              << ";; BV [XOR_RUD1_ALL_INC_REC] => generate the ALL_INC\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X_R) (REC_RAND_VAR var_y Times Y_R) (REC_ALL_INC var_x Times X_A) (REC_ALL_INC var_y Times Y_A) (RAND_NUMBER Times RAND_NUM) (XOR_RUD1_ALL_INC X_A Y_A X_R Y_R RAND_NUM XY) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times)) (REC_ALL_INC var_z Times XY)))\n"
              << "(rule (=> (and (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times) (= Times_New (bvsub Times "
              << one_ind
              << ")) (not (= Times_New "
              << zero_ind
              << "))) (XOR_RUD1_ALL_INC_REC var_x var_y var_z Times_New)))\n"
              << ";; BV [BV_EQUAL] ;; generate the same bit vector [RAND_VAR] => [RAND_VAR]\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_EQUAL_RAND_REC var_x var_y Times)) (REC_RAND_VAR var_y Times X)))\n"
              << "(rule (=> (and (BV_EQUAL_RAND_REC var_x var_y Times) (= Times_New (bvsub Times "
              << one_ind
              << ")) (not (= Times_New "
              << zero_ind
              << "))) (BV_EQUAL_RAND_REC var_x var_y Times_New)))\n"
              << ";; BV [BV_EQUAL] ;; [ALL_INC] => [ALL_INC]\n"
              << "(rule (=> (and (REC_ALL_INC var_x Times X) (BV_EQUAL_ALL_REC var_x var_y Times)) (REC_ALL_INC var_y Times X)))\n"
              << "(rule (=> (and (BV_EQUAL_ALL_REC var_x var_y Times) (= Times_New (bvsub Times "
              << one_ind
              << ")) (not (= Times_New "
              << zero_ind
              << "))) (BV_EQUAL_ALL_REC var_x var_y Times_New)))\n"
              << ";; BV [BV_ZERO] ;; [RAND]\n"
              << "(rule (=> (and (REC_RAND_VAR var_x Times X) (BV_ZERO_REC var_x var_y Times) (= XY " 
              << zero_bit
              << ")) (REC_RAND_VAR var_y Times XY)))\n"
              << "(rule (=> (and (BV_ZERO_REC var_x var_y Times) (= Times_New (bvsub Times "
              << one_ind
              << ")) (not (= Times_New "
              << zero_ind
              << "))) (BV_ZERO_REC var_x var_y Times_New)))\n"
              << ";; BV [IS EMPTY] [RAND_VAR] ;;;; for the [NO KEY] rule\n"
              << ";(rule (=> (and (REC_RAND_VAR var_x Times X) (= Times "
              << one_ind
              << ") (ISEMPTY X int_bool0)) (BV_IS_EMPTY_REC var_x Times int_bool0)))\n"
              << ";(rule (=> (and (REC_RAND_VAR var_x Times X) (ISEMPTY X int_bool0) (not (= Times "
              << one_ind
              << ")) (= Times_New (bvsub Times "
              << one_ind
              << ")) (BV_IS_EMPTY_REC var_x Times_New int_bool1)) (BV_IS_EMPTY_REC var_x Times (and int_bool0 int_bool1))))\n"
              << "\n";

            f << "; [RULE] define the assign relation\n"
              << "(rule (=> (assign to from) (TDEP to from)))\n"
              << ";(rule (=> (xor_assign_left to from) (assign to from)))\n"
              << ";(rule (=> (xor_assign_right to from) (assign to from)))\n"
              << ";(rule (=> (andor_assign_left to from) (assign to from)))\n"
              << ";(rule (=> (andor_assign_right to from) (assign to from)))\n"
              << ";(rule (=> (not_assign to from) (assign to from)))\n"
              << "(rule (=> (load_assign to from) (assign to from)))\n"
              << "(rule (=> (store_assign to from) (assign to from)))\n"
              << "; [RULE] transitive closure\n"
              << "(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))\n"
              << "\n";
            f << ";;;;;;;;;;;;;;;;;;;;;;;;;; beginning of the [RULE] ;;;;;;;;;;;;;;;;;;;;\n"
              << "; rule: [XOR-RUD1] ;; left operand ;; [RAND] + [ANY]\n"
              << ";A => B, B can only be one clause, only A can use <and> to concatenate different clauses\n"
              << ";;new recursive\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from1)) (DIFF_LABEL from1 from2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (RAND from2)) (DIFF_LABEL from2 from1)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 "
              << zero_bit
              << "))))) (RAND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 "
              << zero_bit 
              << ")))) (CHECK_SAME from1 from2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2)) (BV_SAME_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2)) (BV_SAME_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << ";; define the array for [RAND_VAR]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (not (= int_res1 "
              << zero_bit
              << "))))) (SET_SUM_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (and (and (RAND from1) (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 "
              << zero_bit
              << ")))) (BV_ZERO_REC from1 to Times)))\n"
              << ";; define the array for [ALL_INC]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (or (RAND from1) (RAND from2))) (XOR_RUD1_ALL_INC_REC from1 from2 to Times)))\n"
              << "\n"
              << "; rule [XOR] [KEY_SENSITIVE] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BV_ZERO_REC from1 to Times)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "\n"
              << "; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n";
            f << "; rule [AO-RUD1] [RAND] + [NO_KEY] ;; left operand ;; ;;TYPE\n"
              << ";;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2))) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (or (KEY_IND from2) (RAND from2)) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n"
              << "; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE\n"
              << ";; left operand ;; constraint => ALL_INC_left /\ ALL_INC_right = empty\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n"
              << "; rule [AO-RUD2] ;; right operand ;; [RAND] + [NO KEY] ;; TYPE\n"
              << ";;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (or (KEY_IND from1) (RAND from1))) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_IND from1) (RAND from1)) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n"
              << ";rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "; rule [AO-RUD3] ;;; TYPE\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 "
              << zero_bit
              << "))) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 "
              << zero_bit
              << ")) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n";
            f << "; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; TYPE\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n"
              << "; rule [SID] ;; AND OR  ;; TYPE [AO] +  [SID] + [SID]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              << "\n"
              << "; rule [NOT] RAND -> RAND\n"
              << "(rule (=> (and (not_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (not_assign to from1)  (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "; rule [NOT] SID -> SID\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "; rule [NOT] key_sensitive -> key_sensitive\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times))(BV_EQUAL_ALL_REC from2 to Times)))\n"
              << "\n"
              << "; rule [No KEY];; TO DO ;;; all the computation will have the decided types ;;; [NO KEY] rule is not necessary\n"
              << "(rule (=> (CONSTANT from1) (KEY_IND from1)))\n"
              << ";(rule (=> (and (Time Times) (BVAND_ALL_KEY_REC from1 Times int_res0) (= int_res0 "
              << zero_bit
              << ") (BV_IS_EMPTY_REC from1 Times int_bool0) int_bool0) (KEY_IND from1)))\n"
              << "\n"
              << "; rule [LOAD] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [LOAD] + [KEY_IND]\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [LOAD] + [RAND]\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [STORE] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [STORE] + [KEY_IND]\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [STORE] + [RAND]\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule [binary_constant] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (binary_constant to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "; rule [binary_constant] + [KEY_IND]\n"
              << "(rule (=> (and (binary_constant to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "; rule [binary_constant] + [RAND]\n"
              << "(rule (=> (and (binary_constant to from1) (RAND from1)) (RAND to)))\n"
              << "; rule [binary_constant] array\n"
              << "(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "\n"
              << "; rule <zext>, <imcp> and <trunc> can be regarded as the load assignment\n"
              << "(rule (=> (zext_assign to from1) (load_assign to from1)))\n"
              << "(rule (=> (trunc_assign to from1) (load_assign to from1)))\n"
              << "(rule (=> (icmp_assign to from1) (load_assign to from1)))\n"
              << "(rule (=> (sext_assign to from1) (load_assign to from1)))\n"
              << "\n"
              << ";load_assign, store_assign ===> assign\n"
              << "(rule (=> (load_assign to from1) (assign to from1)))\n"
              << "(rule (=> (store_assign to from1) (assign to from1)))\n"
              << "(rule (=> (and (assign to from1) (assign from1 from2)) (assign to from2)))\n"
              << "\n"
              << "; equal_assign: more general assign, only targeting at equal relation\n"
              << "(rule (=> (assign to from1) (equal_assign to from1)))\n"
              << "(rule (=> (binary_constant to from1) (equal_assign to from1)))\n"
              << "(rule (=> true (equal_assign from1 from1)))\n"
              << "(rule (=> (equal_assign from1 from2) (equal_assign from2 from1)))\n"
              << "(rule (=> (and (equal_assign from1 from2) (equal_assign from2 to)) (equal_assign from1 to)))\n"
              << "\n"
              << "; for rule share ;; and the transition inside load and store\n"
              //<< ";(rule (=> (share_2 from1 from2) (share_2 from2 from1)))\n"
              << "(rule (=> (and (share_3 from from1 from2) (equal_assign from1_e from1) (equal_assign from2_e from2) (or (and (xor_assign_left to from1_e) (xor_assign_right to from2_e)) (and (xor_assign_left to from2_e) (xor_assign_right to from1_e)))) (share_2 to from)))\n"
              //<< ";(rule (=> (and (load_assign to from1) (share from1 from2)) (share to from2)))\n"
              //<< ";(rule (=> (and (load_assign to from1) (share to from2)) (share from1 from2)))\n"
              //<< ";(rule (=> (and (store_assign to from1) (share from1 from2)) (share to from2)))\n"
              //<< ";(rule (=> (and (store_assign to from1) (share to from2)) (share from1 from2)))\n"
              << ";; for rule share symmetric\n"
              //<< ";(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from1) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from1)))\n"
              //<< ";(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from2) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from2)))\n"
              << ";; define the case for HD sensitive (indirect)\n"
              << "(rule (=> (and (share_2 from1 from2) (equal_assign from1_e from1) (equal_assign from2_e from2) (xor_assign_left to from1_e) (xor_assign_right to from2_e) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from2_e)))\n"
              << "(rule (=> (and (share_2 from1 from2) (equal_assign from1 from1_e) (equal_assign from2 from2_e) (xor_assign_left to from2_e) (xor_assign_right to from1_e) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from2_e)))\n"
              << "\n";
        }
        
        void printQuery(raw_fd_ostream &f)
        {
            f << ";query KEY_IND type\n"
              << "(query KEY_IND :print-answer true)\n"
              << ";query KEY_SENSITIVE type\n"
              << "(query KEY_SENSITIVE :print-answer true)\n"
              << ";query RAND type\n"
              << "(query RAND :print-answer true)\n"
              << ";query under HD model, key_sensitive\n"
              << "(query HD_SENSITIVE :print-answer true)\n"
              << "; trach the relation between intermediate var and the input parameters\n"
              << "(declare-rel q1(s))\n"
              << "(rule (=> (and (HD_SENSITIVE from1 from2) (assign to from1)) (q1 to)))\n"
              << ";(rule (=> (HD_SENSITIVE from1 from2) (q1 from1)))\n"
              << ";(query q1 :print-answer true)\n"
              << "\n";
        }
        
        std::map<Instruction*, int> getIDMap(Function &F){
            std::map<Instruction*, int> inst_map;
            Function::iterator f_it;
            BasicBlock::iterator bb_it;
            int inst_num = 1;
            for(f_it = F.begin(); f_it != F.end(); f_it++)
            {
                BasicBlock *bb = &*f_it;
                for(bb_it = bb->begin(); bb_it != bb->end(); bb_it++)
                {
                    Instruction *inst = &*bb_it;
                    inst_map.insert(std::pair<Instruction*, int>(inst, inst_num));
                    inst_num++;
                }
            }
            return inst_map;
        }

        virtual bool runOnFunction(Function &F) {
            /** generate the ID map: instrs => ID (use the input file) **/
            std::map<Instruction*, int> ID_map;
            ID_map = getIDMap(F);

            
            std::vector<std::string> RAND_VAR;
            std::vector<std::string> CONSTANT_VAR;
            std::vector<std::string> KEY_VAR;
            RAND_VAR = InFileTypeSet("RAND", InputFileName);
            CONSTANT_VAR = InFileTypeSet("CONSTANT", InputFileName);
            KEY_VAR = InFileTypeSet("KEY", InputFileName);

            /** set the size of the bitset ==> 4 ; the size of all variables => 4*bitset **/
            unsigned input_bitset;
            unsigned index; // the width of bits to represent "Times"
            unsigned input_s;
            input_bitset = 4;
            input_s = input_bitset * 4;
            
            
            /* temporarily use "compute" as the name of the smt file */
            //std::string funcName = "compute";
            std::string funcName = F.getName().str();
            std::string path;
            path = funcName + ".smt2";
            assert(path.size() && "empty output file path");

            /** attempt to open a stream to the passed path, crash a failure **/
            std::error_code ec;
            raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec, sys::fs::OpenFlags::F_Text);
            /** error code with a value of 0 indicates no error **/
            if(ec.value())
            {
                errs() << "[ERROR] Unable to open file " << path << ": " << ec.message() << '\n';
                exit(EXIT_FAILURE);
            }
            
            /** User Input Key_sensitive data **/
            (*outFile) << "; user specify the sensitive variable\n";
            /** (1) print the RAND_NUM and RAND variable information **/
            /** (2) calculate the bit width of the "Times" **/
            index = assign_num(F, *outFile, ID_map, RAND_VAR, CONSTANT_VAR, KEY_VAR, input_s, input_bitset);
            if(!index)
            {
                /** the func don't own the input which is not in the inlined function **/
                outFile->close();
                delete outFile;
                return false;
            }
            
            /** add the prepared specification to the output datalog file **/
            printSpec(*outFile, input_s, index, input_bitset);
            printRule(*outFile, index, input_bitset);
            
            /** print the sharing register information **/
            Share(*outFile, input_s, F, ShareFileName, ID_map);
            
            
            /** TODO: add more facts **/
            /** genFact **/
            assign::genFact fact(outFile, ID_map, RAND_VAR, CONSTANT_VAR, KEY_VAR, input_s, index, input_bitset);
            fact.visit(F);

            /** PRINT query **/
            printQuery(*outFile);
            (*outFile) << ";###### End Facts\n";
            outFile->close();
            delete outFile;
            
            /** IR was not modified **/
            return false;
        }
    };  /** struct assign **/
    char factArray::ID = 0;
    static RegisterPass<factArray> X("factArray", "datalog based front-end for simple assignment analysis",
            false, /** unmodified CFG **/ 
            true); /** analysis pass **/

