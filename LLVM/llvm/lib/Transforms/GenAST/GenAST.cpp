/***** print code for later datalog output *****/
/***** author: Jingbo Wang ********************/

#define DEBUG_TYPE "GenAST_bobo"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"
#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <fstream>

using namespace llvm;
typedef std::tuple<Instruction*, int> instID;

cl::opt<std::string> outputAST("outputAST", cl::desc("specify the output file storing AST"), cl::value_desc("fileName"), cl::Required);
namespace {
    class GenAST : public FunctionPass {
        public:
            static char ID;
            GenAST(): FunctionPass(ID) {}
            /** Tree Structure **/
            struct TreeNode{
                Instruction *root;
                TreeNode *left;
                TreeNode *right;
            };
            /** check if the string has the suffix **/
            bool hasEnding (std::string const &fullString, std::string const &ending) {
                if (fullString.length() >= ending.length()) {
                    return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
                } else {
                    return false;
                }
            }

            /** print the AST tree by traversing the defined units**/
            TreeNode* traverseAST(Instruction *inst, std::map<Instruction*, int> &inst_map, std::map<Instruction*, TreeNode*> &Instr2TreeNode, Instruction *parent)
            {
                TreeNode *astTree = new TreeNode;
                astTree->root = inst;
                if(Instr2TreeNode.find(inst) != Instr2TreeNode.end())
                    return Instr2TreeNode[inst];
                int count = 0; // marking the left and right children
                if(isa<BinaryOperator>(inst)){
                    Value *op1 = inst->getOperand(0);
                    Value *op2 = inst->getOperand(1);
                    /** for the left operand **/
                    if(Instruction *inst_op1 = dyn_cast<Instruction>(op1))
                    {
                        if(Instr2TreeNode.find(inst_op1) != Instr2TreeNode.end())
                            astTree->left = Instr2TreeNode[inst_op1];
                        else
                            astTree->left = traverseAST(inst_op1, inst_map, Instr2TreeNode, inst);
                    }
                    else
                        astTree->left = nullptr; // the leave node is constant, hence it's null
                    /** for the right operand **/
                    if(Instruction *inst_op2 = dyn_cast<Instruction>(op2)){
                        if(Instr2TreeNode.find(inst_op2) != Instr2TreeNode.end())
                            astTree->right = Instr2TreeNode[inst_op2];
                        else
                            astTree->right = traverseAST(inst_op2, inst_map, Instr2TreeNode, inst);
                    }
                    else
                        astTree->right = nullptr;
                    return astTree;
                }else if(isa<AllocaInst>(inst)){
                    std::string inst_name = inst->getName().data();
                    /** if the string has ".addr", which means it's input argument instead of the intermediate variable **/
                    if(hasEnding(inst_name, "addr"))
                    {
                        /** traverse back to the input arguments **/
                        astTree->left = nullptr;
                        astTree->right = nullptr;
                        return astTree;
                    }else{
                        /** traverse back to the intermediate variable **/
                        int inst_ID = inst_map[inst];
                        int parent_ID = inst_map[parent];
                        std::map<int, Instruction*> inst_ID_map;
                        std::set<int> IDnum;
                        /** gather all the use of that intermediate variable **/
                        Instruction *ID_inst;
                        for(User *U: inst->users())
                        {
                            if(Instruction *inst_u = dyn_cast<Instruction>(U))
                            {
                                if(isa<StoreInst>(inst_u))
                                {
                                    ID_inst = inst_u;
                                }
                            }
                        }
                        /*
                        for(User *U: inst->users())
                        {
                            if(Instruction *inst_u = dyn_cast<Instruction>(U))
                            {
                                errs() << inst_map[inst_u] << "\n";
                                inst_ID_map.insert(std::pair<int, Instruction*>(inst_map[inst_u], inst_u));
                                IDnum.insert(inst_map[inst_u]);
                            }
                        }
                        */
                        /** locate the store before the parent instr **/
                        /*
                        std::set<int>::iterator iter = IDnum.find(parent_ID);
                        Instruction *ID_inst;
                        for(;iter != --IDnum.begin(); --iter)
                        {
                            ID_inst = inst_ID_map.find(*iter)->second;
                            std::string ID_inst_name(ID_inst->getOpcodeName());
                            if(ID_inst_name.compare("store") == 0)
                                break;
                        }
                        */
                        if(Instruction *store_op0 = dyn_cast<Instruction>(ID_inst->getOperand(0)))
                            return traverseAST(store_op0, inst_map, Instr2TreeNode, ID_inst);
                        else{
                            std::cerr << "The thing to store is a constant!!!!\n";
                            return nullptr;
                        }
                    }
                }else{
                    /** we assume that the remaining ones are all single operator **/
                    if(Instruction *singleOp = dyn_cast<Instruction>(inst->getOperand(0)))
                        return traverseAST(singleOp, inst_map, Instr2TreeNode, inst);
                    else{
                        std::cerr << "The signle operator handles a constant!!!!\n";
                        return nullptr;
                    }
                }
            }
        
        void printASTree(TreeNode* astTree, std::map<Instruction*, int> &inst_map, int space_cnt, std::ostream &outfile, std::map<Instruction*, TreeNode*> &Instr2TreeNode)
            {
                /** write the AST tree information to the output file **/
                if(astTree == nullptr){
                    //outfile.close();
                    return;
                }
                else{
                    Instruction *root = astTree->root;
                    for(int i = 0; i < space_cnt; i++)
                    {
                        std::cerr << "\t"; outfile << "\t";
                    }
                    std::cerr << inst_map[root] << " " << root->getOpcodeName() <<std::endl;
                    outfile << std::to_string(inst_map[root]);
                    outfile << " ";
                    outfile << root->getOpcodeName();
                    outfile << "\n";
                    //outfile.close();
                }
                /** print the left and right tree **/
                ++space_cnt;
                if(Instr2TreeNode.find(astTree->root) != Instr2TreeNode.end())
                    return;
                else{
                    printASTree(astTree->left, inst_map, space_cnt, outfile, Instr2TreeNode);
                    printASTree(astTree->right, inst_map, space_cnt, outfile, Instr2TreeNode);
                }
            }
        
            void rmRedundant(std::map<Instruction*, TreeNode*> &Instr2TreeNode)
            {
                for(std::map<Instruction*, TreeNode*>::iterator it = Instr2TreeNode.begin(); it != Instr2TreeNode.end();)
                {
                    bool rmFlag = true;
                    for(User *U: (it->first)->users())
                    {
                        if(Instruction *inst_u = dyn_cast<Instruction>(U))
                        {
                            if(Instr2TreeNode.find(inst_u) != Instr2TreeNode.end())
                                rmFlag &= true;
                            else{
                                rmFlag &= false; break;
                            }
                        }
                    }
                    // Delete those nodes which are already used before
                    if(rmFlag)
                        Instr2TreeNode.erase(it++);
                    else
                        ++it;
                }
            }
        
        
            /** runOnFunction **/
            virtual bool runOnFunction(Function &F)
            {
                /** print function name **/
                std::cerr << "Function " << F.getName().str() << "\n";
                //static int bb_number = 1;
                int bb_number = 1;
                //static int inst_number = 1;
                int inst_number = 1;
                std::map<BasicBlock*, int> bb_map;
                std::map<Instruction*, int> inst_map;
                std::map<Instruction*, TreeNode*> Instr2TreeNode;
                Function::iterator f_it;
                BasicBlock::iterator bb_it;

                /** assign numbers to each BasicBlock and Instruction **/
                for(f_it = F.begin(); f_it != F.end(); f_it++)
                {
                    BasicBlock *bb = &*f_it;
                    bb_map.insert(std::pair<BasicBlock*, int>(bb, bb_number));
                    bb_number++;
                    for(bb_it = bb->begin(); bb_it != bb->end(); bb_it++)
                    {
                        Instruction *inst = &*bb_it;
                        inst_map.insert(std::pair<Instruction*, int>(inst, inst_number));
                        inst_number++;
                    }
                }

                /** print BB/Inst  with its number **/
                for(f_it = F.begin(); f_it != F.end(); f_it++)
                {
                    BasicBlock *bb = &*f_it;
                    //std::cerr << "\n" << "BasicBlock " << bb_map[bb] << "\n";
                    errs() << "\n" << (bb->getName()) << "\n";
                    Instruction *parent_inst = bb->begin();
                    for(bb_it = bb->begin(); bb_it != bb->end(); bb_it++)
                    {
                        Instruction *inst = &*bb_it;
                        int num = inst_map[inst];
                        const char *opcode_name = inst->getOpcodeName();
                        if(isa<BinaryOperator>(inst))
                        {
                            std::cerr << "That's a binary operator!" << std::endl;
                        }
                        /** bobo: print the result operand name **/
                        //std::cerr << inst->getName().data() << std::endl;
                        /** print the use-def chain **/
                        /*
                        std::cerr << "print the operands of the corresponding instrucion" << std::endl;
                        for(Use &U: inst->operands())
                        {
                            Value *v = U.get();
                            if(isa<Instruction>(v))
                            {
                                Instruction* inst_v = dyn_cast<Instruction>(v);
                                std::cerr << inst_map[inst_v] << std::endl;
                            }
                        }
                        */
                        /** print the def-use chain **/
                        /*
                        errs() << "this instruction is used in the following instructions \n";
                        for(User *U: inst->users())
                        {
                            if(Instruction *inst_u = dyn_cast<Instruction>(U))
                            {
                                errs() << inst_map[inst_u] << "\n";
                            }
                        }
                        */
                        
                        /** print the operands **/
                        std::cerr << "%" << num << ":" << opcode_name;
                        User::op_iterator op_it;
                        for(op_it = inst->op_begin(); op_it != inst->op_end(); op_it++)
                        {
                            Use *u = &*op_it;
                            Value *v = u->get();
                            if(isa<Instruction>(u))
                                std::cerr << " %" << inst_map[(Instruction*) v];
                            else if(v->hasName())
                                std::cerr << " %" << v->getName().str();
                            else if (ConstantInt* CI = dyn_cast<ConstantInt>(u))
                            {
                                if (CI->getBitWidth() <= 32) {
                                 int constIntValue = CI->getSExtValue();
                                    std::cerr << " " << std::to_string(constIntValue);
                                }else
                                    std::cerr << " XXX";
                            }
                            else
                                std::cerr << " XXX";
                        }
                        std::cerr << "\n";
                        /** print the AST tree of the binary instruction **/
                        if(isa<BinaryOperator>(inst))
                        {
                            std::cerr << "############# Print the AST tree of this binary operation ###############" << std::endl;
                            TreeNode* astTree = traverseAST(inst, inst_map, Instr2TreeNode, nullptr);
                            std::ofstream outfile;
                            outfile.open(outputAST, std::ofstream::out | std::ofstream::app);
                            printASTree(astTree, inst_map, 0, outfile, Instr2TreeNode);
                            Instr2TreeNode.insert(std::pair<Instruction*, TreeNode*>(inst, astTree));
                            rmRedundant(Instr2TreeNode);
                        }
                    }
                }
                std::cerr << "\n";
                return false;
            }

            /** print for later use **/
            virtual void print(std::ostream &O, const Module *M) const {
                O << "This is the GenAST procedure.\n";
            }

            /** preserve all analysis **/
            virtual void getAnalysisUsage(AnalysisUsage &AU) const {
                AU.setPreservesAll();
            };
    };
    char GenAST::ID = 0;
    /** register the GenAST Pass **/
    RegisterPass<GenAST> X("GenAST", "generate AST", true, false);
}
