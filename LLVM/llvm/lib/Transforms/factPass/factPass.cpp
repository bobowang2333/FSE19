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

    struct factPass : public FunctionPass {
        static char ID;
        factPass() : FunctionPass(ID) {}

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
        
        void printShare(raw_fd_ostream &f, std::map<int, share_pair> &pair_map)
        {
            //test
            unsigned tmp = 0;
            for (std::map<int, share_pair>::iterator it = pair_map.begin(); it != pair_map.end(); ++it) {
                //if(tmp > 100)
                  //  break;
                // ++tmp;
                std::string fact;
                fact = "(rule (share " + std::get<2>(it->second) + " " + std::get<3>(it->second) + "))";
                f << ";share_register_variable_pair: " << std::get<0>(it->second) << " " << std::get<1>(it->second) << "\n";
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
              << "; assignment (assign from to)\n"
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
              << "(declare-rel share(s s))\n"
              << "(declare-rel binary_constant(s s))\n"
              << "(declare-rel equal_assign (s s))\n"
              << "\n"
              << "; declare the types which are gonna be used\n"
              << "(declare-rel KEY_SENSITIVE (s))\n"
              << "(declare-rel KEY_IND (s))\n"
              << "(declare-rel CONSTANT (s))\n"
              << "(declare-rel RAND (s))\n"
              << "(declare-rel HD_SENSITIVE (s s))\n"
              << "(declare-rel HD_SENSITIVE_2 (s s))\n"
              << "\n"
              << "; define the TYPE array\n"
              << "(declare-rel RAND_NUMBER (ind BitSet))\n"
              << "(declare-rel KEY_NUMBER (ind BitSet))\n"
              << "(declare-rel REC_RAND_VAR (s ind BitSet))\n"
              << "(declare-rel REC_ALL_INC (s ind BitSet))\n"
              << "(declare-rel Time (ind))\n"
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
              /*
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
              */
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
              /*
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
              */
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
              /*
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
              */
              << "\n";

            f << "; [RULE] define the assign relation\n"
              << "(rule (=> (assign to from) (TDEP to from)))\n"
              //<< ";(rule (=> (xor_assign_left to from) (assign to from)))\n"
              //<< ";(rule (=> (xor_assign_right to from) (assign to from)))\n"
              // << ";(rule (=> (andor_assign_left to from) (assign to from)))\n"
              //<< ";(rule (=> (andor_assign_right to from) (assign to from)))\n"
              //<< ";(rule (=> (not_assign to from) (assign to from)))\n"
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
              /*
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
              */
              << "\n"
              << "; rule [XOR] [KEY_SENSITIVE] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BV_ZERO_REC from1 to Times)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (Time Times) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              */
              << "\n"
              << "; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n";
            f << "; rule [AO-RUD1] [RAND] + [SID] ;; left operand ;; ;;TYPE\n"
              << ";;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;; TYPE\n"
              << ";; left operand ;; constraint => ALL_INC_left /\ ALL_INC_right = empty\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from2) (RAND from1) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_IND] ;; TYPE\n"
              << ";;;; change (not (KEY_SENSITIVE xxx)) = (or (IND) (RAND));;;;;;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_IND from1)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << ";rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from2) (KEY_SENSITIVE from1) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule [AO-RUD3] ;;; TYPE [RAND] + [RAND]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from1 from2)))\n"
            
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2)) (DIFF_LABEL from2 from1)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 "
              << zero_bit
              << "))) (KEY_IND to)))\n"
            //<< ";; this rule may conflict with the rule [RAND] + [NO KEY] and no intersection is a more strict conidtion for key_sensitive type\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (and (and (BV_DIFF_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (BV_DIFF_REC from2 from1 Times int_res1) (= int_res1 "
              << zero_bit
              << ")))) (CHECK_SAME from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (Time Times) (RAND from1) (RAND from2) (BV_SAME_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (Time Times) (RAND from1) (RAND from2) (BV_SAME_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
            
            //<< "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times) (BV_DIFF_REC from1 from2 Times int_res0) (BV_DIFF_REC from2 from1 Times int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 "
              //<< zero_bit
              //<< ")) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND from1) (RAND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n";
            f << "; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE] ;; TYPE\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule [SID] ;; AND OR  ;; TYPE [AO] +  [SID] + [SID]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2)) (INTERSECT_LABEL from1 from2)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times) (BV_INTERSECT_REC from1 from2 Times int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BVOR_ALL_REC from1 from2 to Times)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (Time Times)) (BV_ZERO_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule [NOT] RAND -> RAND\n"
              << "(rule (=> (and (not_assign to from1) (RAND from1)) (RAND to)))\n"
              /*
              << "(rule (=> (and (not_assign to from1)  (RAND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (RAND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              */
              << "; rule [NOT] SID -> SID\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              /*
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              */
              << "; rule [NOT] key_sensitive -> key_sensitive\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              /*
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1) (Time Times))(BV_EQUAL_ALL_REC from2 to Times)))\n"
              */
              << "\n"
              << "; rule [No KEY];; TO DO ;;; all the computation will have the decided types ;;; [NO KEY] rule is not necessary\n"
              << "(rule (=> (CONSTANT from1) (KEY_IND from1)))\n"
              /*
              << ";(rule (=> (and (Time Times) (BVAND_ALL_KEY_REC from1 Times int_res0) (= int_res0 "
              << zero_bit
              << ") (BV_IS_EMPTY_REC from1 Times int_bool0) int_bool0) (KEY_IND from1)))\n"
              */
              << "\n"
              /*
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
              */
              << ";rule [assign] + [KET_SENSITIVE]\n"
              << "(rule (=> (and (assign to from) (KEY_SENSITIVE from)) (KEY_SENSITIVE to)))\n"
              << ";rule [assign] + [KEY_IND]\n"
              << "(rule (=> (and (assign to from) (KEY_IND from)) (KEY_IND to)))\n"
              << ";rule [assign] + [RAND]\n"
              << "(rule (=> (and (assign to from) (RAND from)) (RAND to)))\n"
              /*
              << ";rule [assign] array\n"
              << "(rule (=> (and (assign to from) (Time Times)) (BV_EQUAL_ALL_REC from to Times)))\n"
              << "(rule (=> (and (assign to from) (Time Times)) (BV_EQUAL_RAND_REC from to Times)))\n"
              */
              << "\n"
              << "; rule [binary_constant] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (binary_constant to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "; rule [binary_constant] + [KEY_IND]\n"
              << "(rule (=> (and (binary_constant to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "; rule [binary_constant] + [RAND]\n"
              << "(rule (=> (and (binary_constant to from1) (RAND from1)) (RAND to)))\n"
              /*
              << "; rule [binary_constant] array\n"
              << "(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_ALL_REC from1 to Times)))\n"
              << "(rule (=> (and (binary_constant to from1) (Time Times)) (BV_EQUAL_RAND_REC from1 to Times)))\n"
              */
              << "\n"
              << "; rule <zext>, <imcp> and <trunc> can be regarded as the load assignment\n"
              << "(rule (=> (zext_assign to from1) (assign to from1)))\n"
              << "(rule (=> (trunc_assign to from1) (assign to from1)))\n"
              << "(rule (=> (icmp_assign to from1) (assign to from1)))\n"
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
              << "(rule (=> (share from1 from2) (share from2 from1)))\n"
              << "(rule (=> (and (share from from1) (share from1 from2)) (share from from2)))\n"
              /*
              << ";(rule (=> (and (load_assign to from1) (share from1 from2)) (share to from2)))\n"
              << ";(rule (=> (and (load_assign to from1) (share to from2)) (share from1 from2)))\n"
              << ";(rule (=> (and (store_assign to from1) (share from1 from2)) (share to from2)))\n"
              << ";(rule (=> (and (store_assign to from1) (share to from2)) (share from1 from2)))\n"
              */
              << "\n"
              << ";; for rule share symmetric\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from1) (KEY_SENSITIVE from2)) (HD_SENSITIVE to from1)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (share to from2) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from2)))\n"
              << ";; define the case for HD sensitive (indirect)\n"
              << "(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from_e) (xor_assign_right to_e from1) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))\n"
              << "(rule (=> (and (share to from) (equal_assign from_e from) (equal_assign to_e to) (xor_assign_left to_e from1) (xor_assign_right to_e from_e) (KEY_SENSITIVE from1)) (HD_SENSITIVE to from)))\n"
              << "\n"
              << ";;classify two different HD_sensitive types\n"
              << "(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE to from2)) (HD_SENSITIVE_2 to from2)))\n"
              << "(rule (=> (and (load_assign from1 from) (store_assign to from1) (HD_SENSITIVE from2 to)) (HD_SENSITIVE_2 from2 to)))\n"
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
        
        std::map<Instruction*, int> getIDMap(Function &F) {
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
                    // test
                    if((!to.compare("#x00517")) && (!from.compare("#x0002d")))
                    {
                        bool test = true;
                        if(std::find(KEY_SEN_LIST.begin(), KEY_SEN_LIST.end(), from_another) != KEY_SEN_LIST.end())
                            bool key = true;
                    }
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
            //std::string funcName = F.getName().str();
            std::string path;
            path = funcName + ".smt2";
            assert(path.size() && "empty output file path");

            /** attempt to open a stream to the passed path, crash a failure **/
            std::error_code ec;
            raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec, sys::fs::OpenFlags::F_Text);
            raw_fd_ostream *keyFile = new raw_fd_ostream(key_file_name.c_str(), ec, sys::fs::OpenFlags::F_Text);
            /** error code with a value of 0 indicates no error **/
            if(ec.value())
            {
                errs() << "[ERROR] Unable to open file " << path << ": " << ec.message() << '\n';
                exit(EXIT_FAILURE);
            }
            
            /** add the prepared specification to the output datalog file **/
            //printSpec(*outFile, input_s, index, input_bitset);
            //printRule(*outFile, index, input_bitset);
            /** PRINT RAND_NUM and KEY_NUM **/
            //printNumber(*outFile, index, index_num, input_bitset, rand_num, key_num);
            
            /** print the sharing register information **/
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
            fact.cal_XorAssign(F, xor_assign);
            keyFile->close();
            //output the HD_SENSITIVE type
            //std::vector<std::string> KEY_SEN_LIST = findKey(KEY_VAR, ID_map, input_s, ID_map, F);
            std::vector<std::string> KEY_SEN_LIST = readKey(key_file_name);
            //calculate the equal assign pair
            std::map<unsigned, unsigned> new_equal_assign;
            std::map<unsigned, std::set<std::string>> ID_find_set;
            std::map<std::string, unsigned> ID_count;
            cal_EqualAssign(F, new_equal_assign, ID_map, input_s);
            
            findEqual(F, ID_map, input_s, new_equal_assign, ID_find_set, ID_count);
            HD_SENSITIVE(*outFile, share_map, xor_assign, KEY_SEN_LIST, ID_map, F, input_s, ID_find_set, ID_count);
            //test
            (*outFile) << xor_assign.size() << "\n";
            //(*outFile) << equal_assign.size() << "\n";
            (*outFile) << share_map.size() << "\n";
            
            /** PRINT query **/
            printQuery(*outFile);
            (*outFile) << ";###### End Facts\n";
            outFile->close();
            delete outFile;
            
            /** IR was not modified **/
            return false;
        }
    };  /** struct assign **/
    char factPass::ID = 0;
    static RegisterPass<factPass> X("factPass", "datalog based front-end for simple assignment analysis",
            false, /** unmodified CFG **/ 
            true); /** analysis pass **/

