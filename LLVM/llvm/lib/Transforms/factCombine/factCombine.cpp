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
typedef std::tuple<std::string, std::string> equal_pair;
typedef std::tuple<std::string, std::string, std::string> xor_pair;
// #define ASSIGNMENT_DEBUG

/** add additional commands for user input to specify the type **/
cl::opt<std::string> InputFileName("input", cl::desc("specify the type file"), cl::value_desc("fileName"), cl::Required);
cl::opt<std::string> ShareFileName("share", cl::desc("specify the shared_variable file"), cl::value_desc("fileName"), cl::Required);

    struct factCombine : public FunctionPass {
        static char ID;
        factCombine() : FunctionPass(ID) {}

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

        /** print the RAND_NUMBER && KEY_NUMBER **/
        void printNumber(raw_fd_ostream &f, unsigned input_ind, unsigned input_num, unsigned input_bitset, unsigned rand_n, unsigned key_n){
            unsigned tmp1, tmp, rand_4bit, key_4bit;
            //std::string time = "#b" + ToBitVecForm((1 << (input_ind - 1)), input_ind);
            std::string time = "#b" + ToBitVecForm_original(input_num, input_ind);
            time = "(rule (Time " + time + "))" + "\n";
            f << time;
            for(unsigned j = 1; j <= input_num; j++)
            {
                std::string id = "#b" + ToBitVecForm_original(j, input_ind);
                rand_4bit = rand_n >> ((j-1) * input_bitset);
                tmp1 = (1 << input_bitset) - 1; /* #b1111 */
                tmp = rand_4bit & tmp1;
                std::string rand_s = "#b" + ToBitVecForm_original(tmp, input_bitset);
                rand_s = "(rule (RAND_NUMBER " + id + ' ' + rand_s + "))" + "\n";
                f << rand_s;
                key_4bit = key_n >> ((j-1) * 4);
                tmp1 = (1 << input_bitset) - 1;
                tmp = key_4bit & tmp1;
                std::string key_s = "#b" + ToBitVecForm_original(tmp, input_bitset);
                key_s = "(rule (KEY_NUMBER " + id + ' ' + key_s + "))" + "\n";
                f << key_s;
            }
        }
        
        void printIDMAP(Function &F, raw_fd_ostream &f, std::map<Instruction*, int> &ID_map, unsigned input_s)
        {
            for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
            {
                Instruction *inst = &*i;
                std::string var_name = inst->getName().str();
                std::string id_str = "#x" + ToBitVecForm(ID_map[inst], input_s);
                f << id_str << " " << var_name << "\n";
            }
        }
        
        /* use the backend information, to get the variable pair which shares the same register */
        void Share(unsigned input_s, Function &F, std::string share_file, std::map<Instruction*, int> &ID_map, std::map<equal_pair, bool> &new_share_map)
        {
            std::map<std::string, std::string> alloca_var_id;
            std::vector<equal_pair> share_map;
            /*iterate Alloca inst and print the name of the instr and the corresponding ID */
            for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
            {
                Instruction *inst = &*i;
                const char *opcode_name = inst->getOpcodeName();
                std::string opcode_str(opcode_name);
                if(opcode_str.compare("alloca"))
                    continue;
                else
                {
                    int num = ID_map[inst];
                    std::stringstream stream;
                    stream << "#x" << std::setfill('0') << std::setw(input_s/4) << std::hex << num;
                    std::string instr_id = stream.str();
                    if(inst->hasName())
                    {
                        std::string var_name = inst->getName().str();
                        alloca_var_id.insert(std::pair<std::string, std::string>(var_name, instr_id));
                    }
                    
                }
            }
            
            // insert all the nodes(variables) to a vector
            std::vector<std::string> all_node;
            /* read the "share_variable.txt" file to gain info */
            std::ifstream fin(share_file);
            std::string s;
            unsigned tmp = 0;
            bool continue_flag = false;
            std::string last_var;
            std::string last_id;
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
                        std::vector<std::string>::iterator it_after, before_cont_it;
                        it_after = it;
                        it_after++;
                        before_cont_it = tokens.end();
                        --before_cont_it;
                        if(it_after == tokens.end())
                            break;
                        if((continue_flag) && (it == tokens.begin()))
                        {
                            std::string share_s2;
                            share_s2 = alloca_var_id[(*it).substr(1, -1)];
                            tmp++;
                            // (share from1 from2) => (share from2 from1)
                            share_map.push_back(std::make_tuple(last_id, share_s2));
                            /*
                            share_map.push_back(std::make_tuple(share_s2, last_id));
                            if(std::find(all_node.begin(), all_node.end(), last_id) == all_node.end())
                                all_node.push_back(last_id);
                            if(std::find(all_node.begin(), all_node.end(), share_s2) == all_node.end())
                                all_node.push_back(share_s2);
                             */
                        }
                        if(((it_after != before_cont_it) && (continue_flag)) || ((it_after != tokens.end()) && (!continue_flag)))
                        {
                            // for the first line ended with "continue"
                            if((!continue_flag) && (!(*before_cont_it).compare("continue")) && (it_after == before_cont_it))
                            {
                                last_var = *it;
                                last_id = alloca_var_id[(*it).substr(1, -1)];
                                break;
                            }
                            std::string share_s1, share_s2;
                            share_s1 = alloca_var_id[(*it).substr(1, -1)];
                            share_s2 = alloca_var_id[(*it_after).substr(1, -1)];
                            tmp++;
                            // (share from1 from2) => (share from2 from1)
                            share_map.push_back(std::make_tuple(share_s1, share_s2));
                            /*
                            share_map.push_back(make_tuple(share_s2, share_s1));
                            if(std::find(all_node.begin(), all_node.end(), share_s1) == all_node.end())
                                all_node.push_back(share_s1);
                            if(std::find(all_node.begin(), all_node.end(), share_s1) == all_node.end())
                                all_node.push_back(share_s2);
                             */
                        }
                        else{
                            // when *it_after is representing the "continue"
                            last_var = *it;
                            last_id = alloca_var_id[(*it).substr(1, -1)];
                        }
                    }
                    // set the continue flag
                    if(std::find(tokens.begin(), tokens.end(), "continue") != tokens.end())
                        continue_flag = true;
                    else
                        continue_flag = false;
                }
            }
            fin.close();
            
            /** (rule (=> (and (share from1 from2) (share from2 to)) (share from1 to)))**/
            calTrans(share_map, new_share_map);
            // use dfs to calculate all the share_pair by searching connnected components
            //calShareSet(share_map, all_node, new_share_map);
        }
        
        void calTrans(std::vector<equal_pair> &share_map, std::map<equal_pair, bool> &new_share_map){
            for(std::vector<equal_pair>::iterator it = share_map.begin(); it != share_map.end(); ++it)
            {
                std::string op1 = std::get<0>(*it);
                std::string op2 = std::get<1>(*it);
                new_share_map.insert(std::pair<equal_pair, bool>(*it, true));
                std::vector<equal_pair>::iterator eit = it;
                ++eit;
                if(eit == share_map.end())
                    break;
                else{
                    std::string next_op1 = std::get<0>(*eit);
                    std::string next_op2 = std::get<1>(*eit);
                    // next1 <===> op1
                    if(!next_op1.compare(op1))
                        new_share_map.insert(std::pair<equal_pair, bool>(std::make_tuple(op2, next_op2), true));
                    else if(!next_op1.compare(op2))
                        new_share_map.insert(std::pair<equal_pair, bool>(std::make_tuple(op1, next_op2), true));
                    else if(!next_op2.compare(op1))
                        new_share_map.insert(std::pair<equal_pair, bool>(std::make_tuple(op2, next_op1), true));
                    else if (!next_op2.compare(op2))
                        new_share_map.insert(std::pair<equal_pair, bool>(std::make_tuple(op1, next_op1), true));
                    else
                        continue;
                }
            }
        }
        
        void printShare(raw_fd_ostream &f, std::map<equal_pair, bool> &pair_map)
        {
            //test
            unsigned tmp = 0;
            f << ";share_register_variable_pair: \n";
            for (std::map<equal_pair, bool>::iterator it = pair_map.begin(); it != pair_map.end(); ++it) {
                //if(tmp > 100)
                  //  break;
                // ++tmp;
                std::string fact;
                fact = "(rule (share " + std::get<0>(it->first) + " " + std::get<1>(it->first) + "))";
                f << fact;
                f << "\n";
            }
        }
        
        void calShareSet(std::vector<equal_pair> &share_map, std::vector<std::string> &all_node, std::vector<equal_pair> &new_share_map){
            std::vector<std::string> marked;
            std::map<std::string, int> id;
            unsigned count = 0;
            for(std::vector<std::string>::iterator it = all_node.begin(); it != all_node.end(); ++it){
                std::string op1 = *it;
                if(std::find(marked.begin(), marked.end(), op1) == marked.end())
                {
                    dfs(share_map, op1, marked, id, count);
                    count++;
                }
            }
            
            //build share map with the transitive feature
            for(std::vector<std::string>::iterator it = all_node.begin(); it != all_node.end(); ++it){
                int id1 = (id.find(*it))->second;
                //new_share_map.push_back(std::make_tuple(*it, *it));
                for(std::vector<std::string>::iterator ait = all_node.begin(); ait != all_node.end(); ++ait){
                    int id2 = (id.find(*ait))->second;
                    if(id1 == id2){
                        if((std::find(new_share_map.begin(), new_share_map.end(), std::make_tuple(*it, *ait)) == new_share_map.end()) || (std::find(new_share_map.begin(), new_share_map.end(), std::make_tuple(*ait, *it)) == new_share_map.end()))
                            new_share_map.push_back(std::make_tuple(*it, *ait));
                    }
                }
            }
        }
        
        
        void dfs(std::vector<equal_pair> &share_map, std::string s, std::vector<std::string> &marked, std::map<std::string, int> &id, unsigned count)
        {
            marked.push_back(s);
            id.insert(std::pair<std::string, int>(s, count));
            for(std::vector<equal_pair>::iterator it = share_map.begin(); it != share_map.end(); it++){
                std::string op1 = std::get<0>(*it);
                if(op1.compare(s))
                    continue;
                else
                {
                    std::string op2 = std::get<1>(*it);
                    if(std::find(marked.begin(), marked.end(), op2) == marked.end())
                        dfs(share_map, op2, marked, id, count);
                }
            }
        }
        
        void printSpec(raw_fd_ostream &f, unsigned input_s, unsigned input_ind, unsigned input_bitset) {
            //Using SMT-LIB
            std::string unsigned_size_bits = std::to_string(sizeof(unsigned) * 2);
            f << "(set-option :fixedpoint.engine datalog)\n"
              << "; this sort is used to define all the relations\n"
              << "(define-sort s () (_ BitVec " << input_s << "))\n"
              << "\n";
            f << "(define-sort BitSet () (_ BitVec " << input_bitset << "))\n" 
              << "(define-sort ind () (_ BitVec " << input_ind << "))\n" 
              << "(declare-rel assign(s s))\n"
              << "(declare-rel xor_assign_left (s s))\n"
              << "(declare-rel xor_assign_right (s s))\n"
            << "(declare-rel andor_assign_left (s s))\n"
            << "(declare-rel andor_assign_right (s s))\n"
            << "(declare-rel not_assign (s s))\n"
            << "(declare-rel load_assign (s s))\n"
            << "(declare-rel store_assign (s s))\n"
            << "(declare-rel zext_assign (s s))\n"
            << "(declare-rel sext_assign (s s))\n"
            << "(declare-rel icmp_assign (s s))\n"
            << "(declare-rel trunc_assign (s s))\n"
            << "(declare-rel share(s s))\n"
            << "(declare-rel binary_constant(s s))\n"
            << "(declare-rel equal_assign (s s))\n"
            << "\n"
            << ";define the needed relation\n"
            << "(declare-rel BV_DIFF_REC (s s BitSet))\n"
            << "(declare-rel BV_SAME_REC (s s BitSet))\n"
            << "(declare-rel BV_ALL_INTERSECT (s s BitSet))\n"
            << "(declare-rel BVOR (BitSet BitSet BitSet))\n"
            << "\n"
            << "; declare the types which are gonna be used\n"
            << "(declare-rel KEY_SENSITIVE (s))\n"
            << "(declare-rel KEY_IND (s))\n"
            << "(declare-rel CONSTANT (s))\n"
            << "(declare-rel RAND (s))\n"
            << "(declare-rel HD_SENSITIVE (s s))\n"
            << "(declare-rel HD_SENSITIVE_2 (s s))\n"
            << "\n"
            << "; declare varibles which are used to define the rules (type:s)\n"
            << "(declare-var var s)\n"
            << "(declare-var prev s)\n"
            << "(declare-var to s)\n"
            << "(declare-var from s)\n"
            << "(declare-var from1 s)\n"
            << "(declare-var from2 s)\n"
            << "(declare-var from3 s)\n"
            << "(declare-var from1_e s)\n"
            << "(declare-var from2_e s)\n"
            << "(declare-var to_e s)\n"
            << "(declare-var from_e s)\n"
            << "(declare-var X BitSet)\n"
            << "(declare-var Y BitSet)\n"
            << "\n"
            << "; declare variables which are used (type: bitSet)\n"
            << "(declare-var int_res0 BitSet)\n"
            << "(declare-var int_res1 BitSet)\n"
            << "(declare-var int_res2 BitSet)\n";
            // define the DEP relation
        }

        void printRule(raw_fd_ostream &f, unsigned input_ind, unsigned input_bitset)
        {
            std::string zero_bit = create_zero(input_bitset);
            std::string zero_ind = create_zero(input_ind);
            std::string one_ind = "#b" + ToBitVecForm_original(1, input_ind);
            f << ";define BVOR\n"
              << "(rule (=> (and true true) (BVOR X Y (bvor X Y))))\n"
              << ";;;;;;;;;;;;;;;;;;;;;;;;;; beginning of the [RULE] ;;;;;;;;;;;;;;;;;;;;\n"
              << ";[RAND] + [ANY]  ===> [XOR]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (or (and (RAND from1) (BV_DIFF_REC from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (RAND from2) (BV_DIFF_REC from2 from1 int_res1) (not (= int_res1 "
              << zero_bit
              << "))))) (RAND to)))\n"
              << "\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (and (and (RAND from1) (BV_DIFF_REC from1 from2  int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_DIFF_REC from2 from1 int_res1) (= int_res1 "
              << zero_bit
              << "))) (BV_SAME_REC from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (and (and (RAND from1) (BV_DIFF_REC from1 from2  int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_DIFF_REC from2 from1 int_res1) (= int_res1 "
              << zero_bit
              << "))) (BV_SAME_REC from1 from2 int_res0) (not (= int_res0 #b0000))) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[KEY_SENSITIVE] + [KEY_SENSITIVE] ======> [XOR]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[SID] + [SID] ====> [XOR]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              /*
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
            */
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << ")) (BV_SAME_REC from1 from2 int_res1) (= int_res1 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << ")) (BV_SAME_REC from1 from2 int_res1) (not (= int_res1 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[KEY_SENSITIVE] + [KEY_IND] ======> [XOR]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (or (and (KEY_IND from1) (KEY_SENSITIVE from2)) (and (KEY_IND from2) (KEY_SENSITIVE from1)))) (KEY_SENSITIVE to)))\n"
              << ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;for the [RULE] of and ;;;;;;;;;;;\n"
              << ";[RAND] + [SID] =====> [ANDOR]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (and (RAND from1) (KEY_IND from2)) (and (RAND from2) (KEY_IND from1))) (BV_ALL_INTERSECT from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2)  (BV_ALL_INTERSECT from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[RAND] + [RAND] =====> [ANDOR]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (or (and (BV_DIFF_REC from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (BV_DIFF_REC from2 from1 int_res1) (not (= int_res1 "
              << zero_bit
              << "))))) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (and (and (BV_DIFF_REC from1 from2  int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (BV_DIFF_REC from2 from1 int_res1) (= int_res1 "
              << zero_bit
              << "))) (BV_SAME_REC from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (and (and (BV_DIFF_REC from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (BV_DIFF_REC from2 from1 int_res1) (= int_res1 "
              << zero_bit
              << "))) (BV_SAME_REC from1 from2 int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[KEY_SENSITIVE] + [any]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (or (KEY_SENSITIVE from1) (KEY_SENSITIVE from2))) (KEY_SENSITIVE to)))\n"
              << "\n"
              << ";[SID] + [SID]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2 int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2  int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
            */
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2  int_res0) (not (= int_res0 "
              << zero_bit
              << ")) (BV_SAME_REC from1 from2 int_res1) (= int_res1 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (BV_ALL_INTERSECT from1 from2  int_res0) (not (= int_res0 "
              << zero_bit
              << ")) (BV_SAME_REC from1 from2 int_res1) (not (= int_res1 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "\n";
            f << "; for load, store, binary_constant, sext, zext\n"
              << "(rule (=> (load_assign from1 from2) (assign from1 from2)))\n"
              << "(rule (=> (store_assign from1 from2) (assign from1 from2)))\n"
              << "(rule (=> (binary_constant from1 from2) (assign from1 from2)))\n"
              << "(rule (=> (sext_assign from1 from2) (assign from1 from2)))\n"
              << "(rule (=> (zext_assign from1 from2) (assign from1 from2)))\n"
              << "(rule (=> (trunc_assign from1 from2) (assign from1 from2)))\n"
              << "\n"
              << "; type inference for the assign relation\n"
              << "(rule (=> (and (KEY_SENSITIVE from1) (assign from2 from1)) (KEY_SENSITIVE from2)))\n"
              << "(rule (=> (and (KEY_IND from1) (assign from2 from1)) (KEY_IND from2)))\n"
              << "(rule (=> (and (RAND from1) (assign from2 from1)) (RAND from2)))\n"
              << "\n"
              << "; define the equal_assign relation\n"
              << "(rule (=> (load_assign from1 from2) (equal_assign from1 from2)))\n"
              << "(rule (=> (store_assign from1 from2) (equal_assign from1 from2)))\n"
              << "(rule (=> (sext_assign from1 from2) (equal_assign from1 from2)))\n"
              << "(rule (=> (zext_assign from1 from2) (equal_assign from1 from2)))\n"
              << "(rule (=> (trunc_assign from1 from2) (equal_assign from1 from2)))\n"
              << "\n"
              << ";;;\n"
              << "(rule (=> (and (equal_assign from1 from2) (equal_assign from2 from3)) (equal_assign from1 from3)))\n"
              << "(rule (=> (equal_assign from1 from2) (equal_assign from2 from1)))\n"
              << "\n"
              << ";; define the HD_SENSITIVE\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to_e from2_e) (equal_assign from2 from2_e) (equal_assign to to_e) (KEY_SENSITIVE from1)) (HD_SENSITIVE to_e from2_e)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share from2_e to_e) (equal_assign from2 from2_e) (equal_assign to to_e) (KEY_SENSITIVE from1)) (HD_SENSITIVE to_e from2_e)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to_e from1_e) (equal_assign from1 from1_e) (equal_assign to to_e) (KEY_SENSITIVE from2)) (HD_SENSITIVE to_e from1_e)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share from1_e to_e) (equal_assign from1 from1_e) (equal_assign to to_e) (KEY_SENSITIVE from2)) (HD_SENSITIVE to_e from1_e)))\n"
              << "\n"
              << ";;define the constant type\n"
              << "(rule (=> (CONSTANT from1) (KEY_IND from1)))\n"
              << "\n"
              << ";;define the HD_SENSITIVE_2 type\n"
              << "(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE to from2)) (HD_SENSITIVE_2 to from2)))\n"
              << "(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE from2 to)) (HD_SENSITIVE_2 from2 to)))\n";
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
              << "(query HD_SENSITIVE_2 :print-answer true)\n"
              /*
              << "; trach the relation between intermediate var and the input parameters\n"
              << ";(declare-rel q1(s))\n"
              << ";(rule (=> (and (HD_SENSITIVE from1 from2) (assign to from1)) (q1 to)))\n"
              << ";(rule (=> (HD_SENSITIVE from1 from2) (q1 from1)))"
              << ";(query q1 :print-answer true)\n"
              */
              << "\n";
        }
        
        std::map<Instruction*, int> getIDMap(Function &F){
            std::map<Instruction*, int> inst_map;
            Function::iterator f_it;
            BasicBlock::iterator bb_it;
            static int inst_num = 1;
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
        
        void HD_SENSITIVE(raw_fd_ostream &f, std::map<equal_pair, bool> &share_map, std::vector<xor_pair> &xor_assign, std::vector<std::string> &KEY_SEN_LIST, std::map<Instruction*, int> &IDMap, Function &F, unsigned input_s, std::map<unsigned, std::set<std::string>> &ID_find_set, std::map<std::string, unsigned> &ID_count)
        {
            IfShare(f, xor_assign, share_map, KEY_SEN_LIST, IDMap, F, input_s, ID_find_set, ID_count);
        }
        
        /*
        std::vector<std::string> findEqual(std::vector<equal_pair> &equal_assign, std::string toFind)
        {
            std::vector<std::string> res;
            // (=> (equal_assign from1 from2) (equal_assign from2 from1))
            for(std::vector<equal_pair>::iterator it = equal_assign.begin(); it != equal_assign.end(); it++)
            {
                std::string op1 = std::get<0>(*it);
                std::string op2 = std::get<1>(*it);
                if((!op1.compare(toFind)) && (std::find(res.begin(), res.end(), op2) == res.end()))
                {
                    res.push_back(op2);
                }
         
                //else if((!op2.compare(toFind)) &&(std::find(res.begin(), res.end(), op1) == res.end())) {
                ////////
                //    res.push_back(op1);
               // }
         
                else{
                    continue;
                }
            }
            //res.push_back(toFind);
            return res;
        }
        */
        
        void findEqual(Function &F, std::map<Instruction*, int> &IDMap, unsigned input_s, std::map<unsigned, unsigned> &new_equal_assign, std::map<unsigned, std::set<std::string>> &ID_find_set, std::map<std::string, unsigned> &ID_count)
        {
            std::map<std::string, bool> marked;
            //std::map<std::string, unsigned> ID_count;
            unsigned count = 0;
            for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
            {
                Instruction *inst = &*i;
                unsigned inst_num = IDMap[inst];
                std::string inst_str = "#x" + ToBitVecForm(inst_num, input_s);
                std::set<std::string> ID_find;
                if(marked.find(inst_str) == marked.end()){
                    equal_dfs(marked, IDMap, ID_count, count, new_equal_assign, ID_find, inst_num, input_s);
                    count++;
                    //construct the ID_find_set
                    unsigned insert_count;
                    insert_count = count - 1;
                    ID_find_set.insert(std::pair<unsigned, std::set<std::string>>(insert_count, ID_find));
                }
            }
            //return ID_count;
        }
        
        void equal_dfs(std::map<std::string, bool> &marked, std::map<Instruction*, int> &IDMap, std::map<std::string, unsigned> &ID_count, unsigned count, std::map<unsigned, unsigned> &new_equal_assign, std::set<std::string> &ID_find, unsigned toFind_num, unsigned input_s){
            // set the marked and ID_count array, set the std::string for the node to find
            std::string toFind = "#x" + ToBitVecForm(toFind_num, input_s);
            marked.insert(std::pair<std::string, bool>(toFind, true));
            ID_count.insert(std::pair<std::string, unsigned>(toFind, count));
            // make the set for ID_find
            ID_find.insert(toFind);
            // for (toFind, x)
            if(new_equal_assign.find(toFind_num) != new_equal_assign.end()){
                unsigned adjacent = (new_equal_assign.find(toFind_num))->second;
                std::string adjacent_str = "#x" + ToBitVecForm(adjacent, input_s);
                if(marked.find(adjacent_str) == marked.end())
                {
                    equal_dfs(marked, IDMap, ID_count, count, new_equal_assign, ID_find, adjacent, input_s);
                    new_equal_assign.erase(toFind_num);
                }
            }
            
            //for (x, toFind)
            std::set<unsigned> tofind_neighbour;
            for(std::map<unsigned, unsigned>::iterator it = new_equal_assign.begin(); it != new_equal_assign.end(); ++it){
                if((it->second) == toFind_num)
                    tofind_neighbour.insert(it->first);
            }
            
            for(std::set<unsigned>::iterator it = tofind_neighbour.begin(); it!= tofind_neighbour.end(); it++)
            {
                std::string adjacent_str = "#x" + ToBitVecForm(*it, input_s);
                if(marked.find(adjacent_str) == marked.end())
                    equal_dfs(marked, IDMap, ID_count, count, new_equal_assign, ID_find, *it, input_s);
                new_equal_assign.erase(*it);
            }
            
        }
        
        // given the two equal sets, decide if they share the register or not
        void xor_share(std::map<equal_pair, bool> &share_map, std::set<std::string> &to_equal, std::set<std::string> &from_equal, std::set<equal_pair> &HD_SENSITIVE, std::vector<std::string> &KEY_SEN_LIST, std::string from_another){
            for(std::set<std::string>::iterator it = to_equal.begin(); it != to_equal.end();++it)
            {
                std::string to = *it;
                for(std::set<std::string>::iterator fit = from_equal.begin(); fit != from_equal.end(); ++fit)
                {
                    std::string from = *fit;
                    if((share_map.find(std::make_tuple(to, from)) != share_map.end()) && (std::find(KEY_SEN_LIST.begin(), KEY_SEN_LIST.end(), from_another) != KEY_SEN_LIST.end()))
                        HD_SENSITIVE.insert(std::make_tuple(to, from));
                    else if((share_map.find(std::make_tuple(from, to)) != share_map.end()) && (std::find(KEY_SEN_LIST.begin(), KEY_SEN_LIST.end(), from_another) != KEY_SEN_LIST.end()))
                        HD_SENSITIVE.insert(std::make_tuple(to, from));
                    else
                        continue;
                }
            }
        }
        
        void IfShare(raw_fd_ostream &f, std::vector<xor_pair> &xor_assign, std::map<equal_pair, bool> &share_map, std::vector<std::string> &KEY_SEN_LIST, std::map<Instruction*, int> &IDMap, Function &F, unsigned input_s, std::map<unsigned, std::set<std::string>> &ID_find_set, std::map<std::string, unsigned> &ID_count)
        {
            for(std::vector<xor_pair>::iterator it = xor_assign.begin(); it != xor_assign.end();++it)
            {
                std::set<equal_pair> HD_SENSITIVE_pair;
                std::string to = std::get<0>(*it);
                std::string from1 = std::get<1>(*it);
                std::string from2 = std::get<2>(*it);
                // to and from1 <XOR>
                std::set<std::string> to_equal, from1_equal, from2_equal;
                findEqualID(to, ID_count, to_equal, ID_find_set);
                findEqualID(from1, ID_count, from1_equal, ID_find_set);
                xor_share(share_map, to_equal, from1_equal, HD_SENSITIVE_pair, KEY_SEN_LIST, from2);
                // to and from2 <XOR>
                findEqualID(from2, ID_count, from2_equal, ID_find_set);
                xor_share(share_map, to_equal, from2_equal, HD_SENSITIVE_pair, KEY_SEN_LIST, from1);
                //write to the output file
                if(HD_SENSITIVE_pair.empty())
                    continue;
                else{
                    for(std::set<equal_pair>::iterator hit = HD_SENSITIVE_pair.begin(); hit != HD_SENSITIVE_pair.end(); hit++)
                    {
                        std::string output = "HD_SENSITIVE " + std::get<0>(*hit) + ' ' + std::get<1>(*hit) + "\n";
                        f << output;
                    }
                }
            }
        }
        
        void findEqualID(std::string share_1, std::map<std::string, unsigned> &ID_count, std::set<std::string> &share_1_equal, std::map<unsigned, std::set<std::string>> &ID_find_set)
        {
            unsigned id;
            if(ID_count.find(share_1) != ID_count.end())
                id = (ID_count.find(share_1))->second;
            if(ID_find_set.find(id) != ID_find_set.end())
                share_1_equal = (ID_find_set.find(id))->second;
        }
        
        
        bool hasEnding (std::string fullString, std::string ending) {
            if (fullString.length() >= ending.length()) {
                return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
            } else {
                return false;
            }
        }
        
        void cal_EqualAssign(Function &F, std::map<unsigned, unsigned> &new_equal_assign, std::map<Instruction*, int> &IDMap, unsigned input_s)
        {
            //std::vector<equal_pair> equal_assign;
            std::map<std::string, bool> all_node;
            for(inst_iterator i = inst_begin(F); i != inst_end(F); i++)
            {
                Instruction *inst = &*i;
                unsigned to_num, from_num;
                int inst_num = IDMap[inst];
                to_num = inst_num;
                //std::string to_str = "#x" + ToBitVecForm(inst_num, input_s);
                //std::string from_str;
                const char *opcode_name = inst->getOpcodeName();
                std::string opName(opcode_name);
                /** for the load, store zext trunc and icmp instr **/
                
                 if(!opName.compare("store"))
                 {
                     StoreInst *inst_val = cast<StoreInst>(inst);
                     Value *val = inst_val->getValueOperand();
                     Value *ptr = inst_val->getPointerOperand();
                     if(isa<Instruction>(ptr) && isa<Instruction>(val))
                     {
                         Instruction *ptr_inst = cast<Instruction>(ptr);
                         Instruction *val_inst = cast<Instruction>(val);
                         //to_str = "#x" + ToBitVecForm(IDMap[ptr_inst], input_s);
                         //from_str = "#x" + ToBitVecForm(IDMap[val_inst], input_s);
                         to_num = IDMap[ptr_inst];
                         from_num = IDMap[val_inst];
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
                         //from_str = "#x" + ToBitVecForm(IDMap[ptr_inst], input_s);
                         from_num = IDMap[ptr_inst];
                     }else
                         continue;
                    }
                 else if((!opName.compare("zext")) || (!opName.compare("trunc")) || (!opName.compare("icmp")))
                 {
                     Value *op1 = inst->getOperand(0);
                     if(isa<Instruction>(op1))
                     {
                         Instruction *op1_inst = cast<Instruction>(op1);
                         //from_str = "#x" + ToBitVecForm(IDMap[op1_inst], input_s);
                         from_num = IDMap[op1_inst];
                     }else
                         continue;
                 }else
                     continue;
                new_equal_assign.insert(std::pair<unsigned, unsigned>(to_num, from_num));
            }
        }
        
        /*
        std::vector<std::string> findKey(std::vector<std::string>  &key_var, std::map<Instruction*, int> &ID_map, unsigned input_s, std::map<Instruction*, int> &IDMap, Function &F)
        {
            std::vector<std::string> res;
            for(std::vector<std::string>::iterator kit = key_var.begin(); kit != key_var.end(); kit++)
            {
                for(std::map<Instruction*, int>::iterator mit = ID_map.begin(); mit != ID_map.end(); ++mit)
                {
                    Instruction *inst = mit->first;
                    const char *opcode_name = inst->getOpcodeName();
                    std::string opcode_str(opcode_name);
                    if(!opcode_str.compare("alloca")){
                        if(inst->hasName())
                        {
                            std::string var_name = inst->getName().str();
                            if(hasEnding(var_name, ".addr"))
                                var_name = var_name.substr(0, var_name.length()-5);
                            if(!var_name.compare(*kit))
                            {
                                std::string toFind = "#x" + ToBitVecForm(ID_map[inst], input_s);
                                //std::vector<std::string> tmp = findEqual(equal_assign, toFind);
                                std::vector<std::string> tmp;
                                findEqual(toFind, F, IDMap, tmp, input_s);
                                res.insert(res.end(), tmp.begin(), tmp.end());
                                break;
                            }
                        }
                    }else
                        break;
                }
            }
            return res;
        }
        */
        std::vector<std::string> readKey(std::string f_name){
            std::ifstream fin(f_name);
            std::vector<std::string> res;
            std::string s;
            while(fin >> s){
                res.push_back(s);
            }
            fin.close();
            return res;
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
            /** print the RAND_NUM and KEY_NUM **/
            unsigned rand_num = (1 << RAND_VAR.size()) - 1;
            unsigned key_num = ((1 << (RAND_VAR.size() + KEY_VAR.size())) - 1) - rand_num;
            std::string RAND_NUM, KEY_NUM;
            /** set the size of the bitset ==> 4 ; the size of all variables => 4*bitset **/
            unsigned input_bitset;
            unsigned index, index_num;
            unsigned input_s;
            input_bitset = 4;

            index_num = ceil(((float)(RAND_VAR.size() + CONSTANT_VAR.size() + KEY_VAR.size()))/4);
            index = calExponent(index_num);
            //index = ceil(sqrt((double)index));
            input_s = input_bitset * 5;
            
            /*generate the share variable info from backend */
            std::map<equal_pair, bool> share_map;
            Share(input_s, F, ShareFileName, ID_map, share_map);
            
            /* temporarily use "compute" as the name of the smt file */
            std::string funcName = "compute";
            std::string key_file_name = "key.txt";
            std::string ID_file_name = "id.txt";
            //std::string funcName = F.getName().str();
            std::string path;
            path = funcName + ".smt2";
            assert(path.size() && "empty output file path");

            /** attempt to open a stream to the passed path, crash a failure **/
            std::error_code ec;
            raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec, sys::fs::OpenFlags::F_Text);
            raw_fd_ostream *keyFile = new raw_fd_ostream(key_file_name.c_str(), ec, sys::fs::OpenFlags::F_Text);
            raw_fd_ostream *IDFile = new raw_fd_ostream(ID_file_name.c_str(), ec, sys::fs::OpenFlags::F_Text);
            /** error code with a value of 0 indicates no error **/
            if(ec.value())
            {
                errs() << "[ERROR] Unable to open file " << path << ": " << ec.message() << '\n';
                exit(EXIT_FAILURE);
            }
            
            /** add the prepared specification to the output datalog file **/
            printSpec(*outFile, input_s, index, input_bitset);
            printRule(*outFile, index, input_bitset);
            /** PRINT RAND_NUM and KEY_NUM **/
            //printNumber(*outFile, index, index_num, input_bitset, rand_num, key_num);
            
            /** print the sharing register information **/
            // Jun 30 Added for testing
            //printShare(*outFile, share_map);
            
            /** User Input Key_sensitive data **/
            (*outFile) << "; user specify the sensitive variable\n";
            /** TODO: add more facts **/
            /** genFact **/
            std::map<Instruction*, std::vector<unsigned>> REC_ALL_INC;
            std::map<Instruction*, std::vector<unsigned>> REC_RAND_VAR;
            //std::vector<unsigned> KEY_SENSITIVE_var;
            std::map<unsigned, bool> RAND_var;
            std::map<unsigned, bool> KEY_SENSITIVE_var;
            std::map<unsigned, bool> KEY_IND_var;
            //std::vector<equal_pair> equal_assign;
            std::map<std::string, std::string> equal_assign;
            std::vector<xor_pair> xor_assign;
            
            assign::genFact fact(outFile, keyFile, ID_map, RAND_VAR, CONSTANT_VAR, KEY_VAR, input_s, index, index_num, input_bitset, REC_ALL_INC, REC_RAND_VAR, RAND_var, KEY_SENSITIVE_var, KEY_IND_var);
            fact.visit(F);
            //fact.cal_EqualAssign(F, equal_assign);
            //fact.cal_XorAssign(F, xor_assign);
            keyFile->close();
            //output the HD_SENSITIVE type
            //std::vector<std::string> KEY_SEN_LIST = findKey(KEY_VAR, ID_map, input_s, ID_map, F);
            std::vector<std::string> KEY_SEN_LIST = readKey(key_file_name);
            //calculate the equal assign pair
            std::map<unsigned, unsigned> new_equal_assign;
            std::map<unsigned, std::set<std::string>> ID_find_set;
            std::map<std::string, unsigned> ID_count;
            //cal_EqualAssign(F, new_equal_assign, ID_map, input_s);
            
            //findEqual(F, ID_map, input_s, new_equal_assign, ID_find_set, ID_count);
            //HD_SENSITIVE(*outFile, share_map, xor_assign, KEY_SEN_LIST, ID_map, F, input_s, ID_find_set, ID_count);
            //test
            //(*outFile) << xor_assign.size() << "\n";
            //(*outFile) << equal_assign.size() << "\n";
            //(*outFile) << share_map.size() << "\n";
            
            /** PRINT query **/
            printQuery(*outFile);
            (*outFile) << ";###### End Facts\n";
            outFile->close();
            delete outFile;
            // DEBUG => print the mapping between variables and their ID
            
            printIDMAP(F, *IDFile, ID_map, input_s);
            IDFile->close();
            
            /** IR was not modified **/
            return false;
        }
    };  /** struct assign **/
    char factCombine::ID = 0;
    static RegisterPass<factCombine> X("factCombine", "datalog based front-end for simple assignment analysis",
            false, /** unmodified CFG **/ 
            true); /** analysis pass **/

