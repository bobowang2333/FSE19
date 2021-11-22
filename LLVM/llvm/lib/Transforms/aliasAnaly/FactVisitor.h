/*
 * Author: Markus Kusano
 *
 * InstVisitor to visit every instruction in the program.
 *
 * This is used to generate facts about each statement used in the program.
 */
#pragma once
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/raw_ostream.h"
#include "utils/ValToStrDB.h"
#include <cstdint>

using namespace llvm;

namespace ciaa {
  class FactVisitor : public InstVisitor<FactVisitor> {
    private:
      // Given a constant in the program, return a string representation
      struct Constants {
        static constexpr char const *const NULL_STR = "NULL";
        static std::string getStr(Constant *c);
      };
      // Output stream to datalog file. Assumed to be opened by the caller of the
      // constructor of this class.
      raw_fd_ostream *datalogFile;

      // If true, only consider pointers which can transitively reach a malloc()
      // call to be in the points to relation. Otherwise, track all pointer
      // relations. See the top of ciaa.cpp for more information
      bool onlyMalloc;

      // If datalog is true, the output will be in datalog format. If it is
      // false, the output will be in smt-lib
      bool datalog;

      // If true, integer IDs will be used instead of strings.
      //
      // This is only true if datalog is false (if SMT-LIB2 is used)
      bool useIntIDs;

      // Add specification to the passed (opened) ostream
      void addDatalogSpec(raw_fd_ostream &f);

      // Function to handle both CallInsts and InvokveInsts
      void handleCallSite(CallSite I);

      // Returns true if the passed function is a call to malloc
      bool isMalloc(Function *f);

      // return the comment character based on the output file type
      char getCommentChar();

      // Returns a string representing an assignment:
      // Assign(<to>, <from>).
      //
      // Automatically extracts the IDs of the passed values and sets up the
      // number of stars to prepend of each ID
      std::string createAssign(Value *to, Value *from);

      // Returns a string representing an assignment:
      // Assign(<to>, <from>).
      std::string createAssign(std::string to, std::string from);

      // Returns a string representing a store fact.
      //
      // This is the same as assignment except the to value (the pointer operand
      // in the store) is dereferenced once. That is:
      //
      // store i8** %argv, i8*** %2, align 8
      //
      // Creates a fact:
      //
      // Assign("**2", "argv").
      //
      // This will cause any subsequent loads of %2 to alias with argv (see
      // createLoad())
      std::string createStore(Value *to, Value *from);

      // Returns a string representing a load fact.
      //
      // This is the same as an assignment but the pointers are dereferenced.
      // That is, to is assigned the value of once dereferenced from.
      //
      // This will crash if the underlying type of from is not a pointer (i.e.,
      // from is not atleast a '**' pointer)
      std::string createLoad(Value *to, Value *from);

      // Return a string representing the assignment of a value to a malloc call.
      // When onlyMalloc is false, this is simply an assignment relation to a new
      // heap object.
      //
      // When onlyMalloc is true, this is a special Allocate() relation
      //
      // Note: every time this function is called a new heap object will be
      // created.
      //std::string createMalloc(std::string to);
      std::string createMalloc(Value *to);

      // Write the passed datalog with a comment containing the passed value
      // above it to the datalogFile
      void writeFact(Value *v, std::string fact);

    public:
      // Constructor: Pass onlyMalloc as true if only instructions which can
      // transitively reach a malloc() instruction should be included in the
      // points-to relation (i.e., only track heap accesses).
      //
      // Otherwise, all pointer arithmetic is tracked. See ciaa.cpp for a more
      // detailed description of the specifications.
      //
      // If datalog is true, the output will be in datalog format. If it is
      // false, the output will be in smt-lib
      //
      // The passed ostream will be used to dump facts to. It is assumed
      // to already be open.
      FactVisitor(bool onlyMalloc, bool datalog, raw_fd_ostream *os);

      // Overridden visitor functions
      void visitReturnInst(ReturnInst &I);
      void visitCallInst(CallInst &I);
      void visitInvokeInst(InvokeInst &I);
      void visitLoadInst(LoadInst &I);
      void visitStoreInst(StoreInst &I);
      void visitAllocaInst(AllocaInst &I);

      // Map of Value*s in the program to IDs. These will be saved in the named
      // metadata section of the program.
      ValToStrDB IDMap;

#if 0
      void visitBranchInst(BranchInst &I);
      void visitSwitchInst(SwitchInst &I);
      void visitIndirectBrInst(IndirectBrInst &I);
      void visitResumeInst(ResumeInst &I);
      void visitUnreachableInst(UnreachableInst &I);
      void visitICmpInst(ICmpInst &I);
      void visitFCmpInst(FCmpInst &I);
      void visitAllocaInst(AllocaInst &I);
      void visitStoreInst(StoreInst &I);
      void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
      void visitAtomicRMWInst(AtomicRMWInst &I);
      void visitFenceInst(FenceInst &I);
      void visitGetElementPtrInst(GetElementPtrInst &I);
      void visitPHINode(PHINode &I);
      void visitTruncInst(TruncInst &I);
      void visitZExtInst(ZExtInst &I);
      void visitSExtInst(SExtInst &I);
      void visitFPTruncInst(FPTruncInst &I);
      void visitFPExtInst(FPExtInst &I);
      void visitFPToUIInst(FPToUIInst &I);
      void visitFPToSIInst(FPToSIInst &I);
      void visitUIToFPInst(UIToFPInst &I);
      void visitSIToFPInst(SIToFPInst &I);
      void visitPtrToIntInst(PtrToIntInst &I);
      void visitIntToPtrInst(IntToPtrInst &I);
      void visitBitCastInst(BitCastInst &I);
      void visitAddrSpaceCastInst(AddrSpaceCastInst &I);
      void visitSelectInst(SelectInst &I);
      void visitVAArgInst(VAArgInst &I);
      void visitExtractElementInst(ExtractElementInst &I);
      void visitInsertElementInst(InsertElementInst &I);
      void visitShuffleVectorInst(ShuffleVectorInst &I);
      void visitExtractValueInst(ExtractValueInst &I);
      void visitInsertValueInst(InsertValueInst &I);
      void visitLandingPadInst(LandingPadInst &I);
      void visitDbgDeclareInst(DbgDeclareInst &I);
      void visitDbgValueInst(DbgValueInst &I);
      void visitDbgInfoIntrinsic(DbgInfoIntrinsic &I);
      void visitMemSetInst(MemSetInst &I);
      void visitMemCpyInst(MemCpyInst &I);
      void visitMemMoveInst(MemMoveInst &I);
      void visitMemTransferInst(MemTransferInst &I);
      void visitMemIntrinsic(MemIntrinsic &I);
      void visitVAStartInst(VAStartInst &I);
      void visitVAEndInst(VAEndInst &I);
      void visitVACopyInst(VACopyInst &I);
      void visitIntrinsicInst(IntrinsicInst &I);

      // Next level propagators: If the user does not overload a specific
      // instruction type, they can overload one of these to get the whole class
      // of instructions...
      //
      void visitCastInst(CastInst &I);
      void visitBinaryOperator(BinaryOperator &I);
      void visitCmpInst(CmpInst &I);
      void visitTerminatorInst(TerminatorInst &I);
      void visitUnaryInstruction(UnaryInstruction &I);
#endif
  };
} // namespace ciaa
