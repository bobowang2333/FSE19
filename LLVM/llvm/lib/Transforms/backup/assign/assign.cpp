/*** simple assignment facts generation ***/
/*** output: z3 fix-point datalog file ***/
/*** author: Jingbo Wang ***/

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "genFact.h"
#include <string>
/** for reading the input specified file **/
#include <vector>
#include <sstream>
#include <iostream>
#include <fstream>

using namespace llvm;
// #define ASSIGNMENT_DEBUG

/** add additional commands for user input to specify the type **/
cl::opt<std::string> InputFileName("input", cl::desc("specify the type file"), cl::value_desc("fileName"), cl::Required);

    struct assignFact : public FunctionPass {
        static char ID;
        assignFact() : FunctionPass(ID) {}

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
            std::ifstream input_file (file_name);
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
        
        std::string ToBitVecForm (unsigned in, unsigned max_len)
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

        void printSpec(raw_fd_ostream &f, unsigned input_s, unsigned input_bitset) {
            //Using SMT-LIB
            std::string unsigned_size_bits = std::to_string(sizeof(unsigned) * 2);
            f << "(set-option :fixedpoint.engine datalog)\n"
              << "; this sort is used to define all the relations\n"
              << "(define-sort s () (_ BitVec " << input_s << "))\n"
              << "\n";
            f << "(define-sort BitSet () (_ BitVec " << input_bitset << "))\n" 
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
              << "\n"
              << "; declare the types which are gonna be used\n"
              << "(declare-rel KEY_SENSITIVE (s))\n"
              << "(declare-rel KEY_IND (s))\n"
              << "(declare-rel CONSTANT (s))\n"
              << "(declare-rel RAND (s))\n"
              << "\n"
              << "; define the TYPE array\n"
              << "(declare-rel RAND_NUMBER (BitSet))\n"
              << "(declare-rel KEY_NUMBER (BitSet))\n"
              << "(declare-rel RAND_VAR (s BitSet))\n"
              << "(declare-rel ALL_INCLUDE (s BitSet))\n"
              << "\n"
              << "; declare varibles which are used to define the rules (type:s)\n"
              << "(declare-var var s)\n"
              << "(declare-var prev s)\n"
              << "(declare-var to s)\n"
              << "(declare-var from s)\n"
              << "(declare-var from1 s)\n"
              << "(declare-var from2 s)\n"
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

        void printRule(raw_fd_ostream &f, unsigned input_s)
        {
            std::string zero_bit = create_zero(input_s);
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
              << "; define the variables used for the function\n"
              << "(declare-var X BitSet)\n"
              << "(declare-var Y BitSet)\n"
              << "(declare-var Z BitSet)\n"
              << "(declare-var X_A BitSet)\n"
              << "(declare-var Y_A BitSet)\n"
              << "(declare-var X_R BitSet)\n"
              << "(declare-var Y_R BitSet)\n"
              << "(declare-var N BitSet)\n"
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
            f << "; [RULE] define the assign relation\n"
              << "(rule (=> (assign to from) (TDEP to from)))\n"
              << "(rule (=> (xor_assign_left to from) (assign to from)))\n"
              << "(rule (=> (xor_assign_right to from) (assign to from)))\n"
              << "(rule (=> (andor_assign_left to from) (assign to from)))\n"
              << "(rule (=> (andor_assign_right to from) (assign to from)))\n"
              << "(rule (=> (not_assign to from) (assign to from)))\n"
              << "(rule (=> (load_assign to from) (assign to from)))\n"
              << "(rule (=> (store_assign to from) (assign to from)))\n"
              << "; [RULE] transitive closure\n"
              << "(rule (=> (and (assign to from) (TDEP from prev)) (TDEP to prev)))\n"
              << "\n";
            f << "; [RULE] define the type inference ;;;;;;;;;;\n"
              << "; rule: [XOR-RUD1] ;; [XOR-RUD2] ;; [RAND] + [ANY]\n"
              << "; A => B, B can only be one clause, only A can use \"and\" to concatenate different clauses\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (not (= int_res1 "
              << zero_bit
              << "))))) (RAND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (and (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (= int_res1 "
              << zero_bit
              << ")))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (not (= int_res1 "
              << zero_bit
              << ")))) (SET_SUM RAND_A RAND_B int_res2)) (RAND_VAR to int_res2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (and (and (RAND from1) (BV_Diff RAND_A ALL_INC_B int_res0) (= int_res0 "
              << zero_bit
              << ")) (and (RAND from2) (BV_Diff RAND_B ALL_INC_A int_res1) (= int_res1 "
              << zero_bit
              << "))) (BV_ZERO RAND_A int_res2)) (RAND_VAR to int_res2)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (RAND_NUMBER RAND_NUM) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (RAND from1) (RAND from2)) (XOR_RUD1_ALL_INC ALL_INC_A ALL_INC_B RAND_A RAND_B RAND_NUM int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "\n"
              << ";rule: [XOR] ;; [KEY_SENSITIVE] + [kEY_SENSITIVE]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "\n"
              << "; rule [XOR] [SID] + [SID] ;; TO DO: refinement ;; overlapping with rule [SID]\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "(rule (=> (and (xor_assign_left to from1) (xor_assign_right to from2) (KEY_IND from1) (KEY_IND from2) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0))  (RAND_VAR to int_res0)))\n"
              << "\n";
            f << "; rule [AO-RUD1] [RAND] + [NO_KEY] ;; left operand ;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from2) (RAND from2)) (RAND from1) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from2) (RAND from2)) (RAND from1) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (or (RAND from2) (KEY_IND from2)) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (or (RAND from2) (KEY_IND from2)) (BV_ZERO RAND_A int_res1)) (RAND_VAR to int_res1)))\n"
              << "\n"
              << "; rule [AO-RUD1] [RAND] + [KEY_SENSITIVE] ;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from2) (RAND from1) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              <<"\n"
              << "; rule [AO-RUD2] ;; right operand ;; [RAND] + [NO KEY] ;;\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from1) (RAND from1)) (RAND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0)  (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (or (KEY_IND from1) (RAND from1)) (RAND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (or (RAND from1) (KEY_IND from1)) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from2) (or (RAND from1) (KEY_IND from1)) (BV_ZERO RAND_B int_res1)) (RAND_VAR to int_res1)))\n"
              << "\n"
              << ";rule [AO-RUD2] ;; right operand ;; [RAND] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_SENSITIVE from1) (RAND from2) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "\n"
              << "; rule [AO-RUD3]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_Diff RAND_A ALL_INC_B int_res0) (BV_Diff RAND_B ALL_INC_A int_res1) (BVOR int_res0 int_res1 int_res2) (not (= int_res2 "
              << zero_bit
              << "))) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_Diff RAND_A ALL_INC_B int_res0) (BV_Diff RAND_B ALL_INC_A int_res1) (BVOR int_res0 int_res1 int_res2) (= int_res2 "
              << zero_bit
              << ")) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (RAND from1) (RAND from2) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "\n";
            f << "; rule [AO] [KEY_SENSITIVE] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B)) (KEY_SENSITIVE to)))"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BVOR ALL_INC_A ALL_INC_B int_res0)) (ALL_INCLUDE to int_res0)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (KEY_SENSITIVE from1) (KEY_SENSITIVE from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "\n"
              << "; rule [SID] ;;; [AND]/[OR] + [SID] + [SID]\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (= int_res0 "
              << zero_bit
              << ")) (KEY_IND to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BV_Intersect ALL_INC_A ALL_INC_B int_res0) (not (= int_res0 "
              << zero_bit
              << "))) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (andor_assign_left to from1) (andor_assign_right to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (BVOR ALL_INC_A ALL_INC_B int_res1)) (ALL_INCLUDE to int_res1)))\n"
              << "(rule (=> (and (assign to from1) (assign to from2) (ALL_INCLUDE from1 ALL_INC_A) (ALL_INCLUDE from2 ALL_INC_B) (KEY_IND from1) (KEY_IND from2) (RAND_VAR from1 RAND_A) (RAND_VAR from2 RAND_B) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "\n"
              << "; rule [NOT] RAND -> RAND\n"
              << "(rule (=> (and (not_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (RAND from1)) (RAND_VAR to RAND_A)))\n"
              << "(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (RAND from1)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "; rule [NOT] SID -> SID\n"
              << "(rule (=> (and (not_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (KEY_IND from1)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (KEY_IND from1)) (RAND_VAR to RAND_A)))\n"
              << "; rule [NOT] key_sensitive -> key_sensitive\n"
              << "(rule (=> (and (not_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (not_assign to from1) (ALL_INCLUDE from1 ALL_INC_A) (KEY_SENSITIVE from1)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (not_assign to from1) (RAND_VAR from1 RAND_A) (KEY_SENSITIVE from1)) (RAND_VAR to RAND_A)))\n"
              << "\n"
              << "; rule [LOAD] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_SENSITIVE from1) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "; rule [LOAD] + [KEY_IND]\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (load_assign to from1) (KEY_IND from1) (RAND_VAR from1 RAND_A) (BV_EQUAL RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "; rule [LOAD] + [RAND]\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (load_assign to from1) (RAND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))\n"
              << "\n"
              << "; rule [STORE] + [KEY_SENSITIVE]\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1)) (KEY_SENSITIVE to)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_SENSITIVE from1) (RAND_VAR from1 RAND_A) (BV_ZERO RAND_A int_res0)) (RAND_VAR to int_res0)))\n"
              << "; rule [STORE] + [KEY_IND]\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1)) (KEY_IND to)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (store_assign to from1) (KEY_IND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))\n"
              << "; rule [STORE] + [RAND]\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1)) (RAND to)))\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1) (ALL_INCLUDE from1 ALL_INC_A)) (ALL_INCLUDE to ALL_INC_A)))\n"
              << "(rule (=> (and (store_assign to from1) (RAND from1) (RAND_VAR from1 RAND_A)) (RAND_VAR to RAND_A)))\n"
              << "\n"
              << "; rule [No KEY]\n"
              << "(rule (=> (and (ALL_INCLUDE from1 ALL_INC_A) (KEY_NUMBER KEY_NUM) (BVAND ALL_INC_A KEY_NUM int_res0) (ISEMPTY int_res0 int_bool0) int_bool0 (RAND_VAR from1 RAND_A) (= RAND_A "
              << zero_bit
              << ")) (KEY_IND from1)))\n"
              << "(rule (=> (CONSTANT from1) (KEY_IND from1)))\n"
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

        virtual bool runOnFunction(Function &F) {
            /** generate the ID map: instrs => ID **/
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
            unsigned input_bitset = (RAND_VAR.size() + KEY_VAR.size());
            unsigned input_s = input_bitset * 2;
            std::string rand_num_s = "#b" + ToBitVecForm(rand_num, input_bitset);
            std::string key_num_s = "#b" + ToBitVecForm(key_num, input_bitset);
            RAND_NUM = "(rule (RAND_NUMBER " + rand_num_s + "))";
            KEY_NUM = "(rule (KEY_NUMBER " + key_num_s + "))";

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

            /** add the prepared specification to the output datalog file **/
            printSpec(*outFile, input_s, input_bitset);
            printRule(*outFile, input_bitset);

            /** PRINT RAND_NUM and KEY_NUM **/
            (*outFile) << RAND_NUM;
            (*outFile) << "\n";
            (*outFile) << KEY_NUM;
            (*outFile) << "\n";
            /** User Input Key_sensitive data **/
            (*outFile) << "; user specify the sensitive variable\n";
            /** TODO: add more facts **/
            /** genFact **/
            assign::genFact fact(outFile, ID_map, RAND_VAR, CONSTANT_VAR, KEY_VAR, input_s, input_bitset);
            fact.visit(F);

            (*outFile) << ";###### End Facts\n";
            outFile->close();
            delete outFile;
            
            /** IR was not modified **/
            return false;
        }
    };  /** struct assign **/
    char assignFact::ID = 0;
    static RegisterPass<assignFact> X("assignFact", "datalog based front-end for simple assignment analysis",
            false, /** unmodified CFG **/ 
            true); /** analysis pass **/

