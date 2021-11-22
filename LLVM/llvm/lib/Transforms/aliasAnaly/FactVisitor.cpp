#include "FactVisitor.h"
#include <string>
#include <cassert>
#include <typeinfo>
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Instructions.h"

#define MK_DEBUG
#include "utils/mk_debug.h"
#include "utils/utils.h"
namespace ciaa {
  FactVisitor::FactVisitor(bool onlyMalloc, bool datalog, raw_fd_ostream *os) {
    this->onlyMalloc = onlyMalloc;
    this->datalog = datalog;
    this->datalogFile = os;

    if (!datalog) {
      // SMT-LIB does not automatically convert strings to integers
      useIntIDs = true;
    }
    else {
      useIntIDs = false;
    }

    // Add a comment indicating that we are starting to dump the facts
    (*os) << getCommentChar() << "#### Begin facts\n";

  }

  // Given the passed name of a function, return the name of its return
  // instruction. This allows for other functions to setup alias links to the
  // return value
  std::string getFuncReturnName(StringRef funcName) {
    assert(funcName.size() 
        && "Size zero function name passed to getFuncReturnName");
    std::string ret = funcName;
    return ret + "_RETURN";
  }

  void FactVisitor::visitReturnInst(ReturnInst &I) {
    DEBUG_MSG("Visiting RetInst: " << I << '\n');
    Value *retVal = I.getReturnValue();
    if (retVal == NULL) {
      // When getReturnValue() returns NULL, there is no value being returned
      return;
    }
    Type *ty = retVal->getType();
    if (!ty->isPointerTy()) {
      // if the function is not returning a pointer there is no need to track
      // alias information of the return
      return;
    }

    // Get the name of the function containing the return inst. Each function
    // has a special return value name which aliases to all the return points
    // of the function
    StringRef funcName = I.getParent()->getParent()->getName();
    assert(funcName.size() && "Returning from function with no name");
    DEBUG_MSG("\tFunction Name: " << funcName << '\n');
    // Identifier for function return
    std::string funcRetName = getFuncReturnName(funcName);

    // Handle the different types of possible pointers returned.
    if (Instruction *retValInst = dyn_cast<Instruction>(retVal)) {
      // Create an assignment from the return value instruction to the return
      // value. This is internal to the function
      //std::string fact1 = createAssign(&I, retValInst);



      // Create an assignment from the value being returned (retValInst) to the global
      // return of the function. This allows for other functions to connect
      // witth the return value.
      //
      // Note: this approximates all return instructions of a function to alias
      // together
      std::string fact = createAssign(funcRetName, IDMap.saveAndGetID(retValInst));

      (*datalogFile) << getCommentChar() << "# Function: " << funcName << "\n" 
                     << getCommentChar() << I << '\n'
                     << fact << '\n';
    }
    else if (ConstantPointerNull *cn = dyn_cast<ConstantPointerNull>(retVal)) {
      std::string constID = FactVisitor::Constants::getStr(cn);
      // The function return is assigned the constant ID
      std::string fact = createAssign(funcRetName, constID);
      (*datalogFile) << getCommentChar() << "# Function: " << funcName << "\n" 
                     << getCommentChar() << I << '\n'
                     << fact << '\n';
    }
    else {
      // TODO: Probably need to handle constant pointer returns (e.g., NULL)
      DEBUG_MSG("[ERROR] Non instruction return: " << *retVal << '\n');
      llvm_unreachable("Non instruction return value (see above)");
    }
  }

  void FactVisitor::visitLoadInst(LoadInst &I) {
    DEBUG_MSG("Visiting load instruction: " << I << '\n');

    // A load instruction is an assignment to the return of the load from the
    // once-dereferenced operand. Only loads of atleast '**' pointers need to be
    // tracked since '*' pointers return a scalar value which does not need to be
    // tracked.

    // Get the type of the value being loaded. This is the type of the return of
    // the load inst
    Type *elementType = I.getType();
    assert(elementType && "NULL underlying type");

    if (!elementType->isPointerTy()) {
      // Skip loads of non-pointer values
      return;
    }

    Value *ptr = I.getPointerOperand();

    std::string fact;
    if (isa<Instruction>(ptr)) {
      fact = createLoad(&I, I.getPointerOperand());
    }
    else {
      errs() << "[ERROR] Pointer Operand: " << *ptr << '\n';
      llvm_unreachable("unhandled load inst operand (see above)");
    }
    assert(fact.size() && "fact not set");

    writeFact(&I, fact);
  }

  void FactVisitor::visitStoreInst(StoreInst &I) {
    DEBUG_MSG("Visiting store instruction: " << I << '\n');

    // A store instruction is of the form:
    // store i8** %argv, i8*** %2, align 8
    //
    // This is an assignment of argv to the dereference of %2, e.g.,
    // *(%2) = argv
    //
    // As a result, we only need to track those store instructions which are
    // storing pointer values (the first operand). Non-pointer stores are simply
    // scalar assignments which we do not need to track.
    //
    // Subsequent load instructions of %2 need to alias to argv

    // Get the value being stored
    Value *val = I.getValueOperand();
    assert(val->getType() != NULL && "NULL type being stored");

    if (!val->getType()->isPointerTy()) {
      // Only track stores of pointer values
      return;
    }
    // Get the pointer operand
    Value *ptr = I.getPointerOperand();

    // Handle different types of values which can be stored
    std::string fact;
    fact = createStore(ptr, val);
    assert(fact.size() && "fact not set");

    writeFact(&I, fact);
  }

  void FactVisitor::visitAllocaInst(AllocaInst &I) {
    assert(I.getType() && "Alloca with NULL type");
    assert(I.getType()->isPointerTy() && "pointer type");

    static int counter = 0;
    // Create the stack object
    std::string stackStr = "stack_" + std::to_string(counter);
    counter += 1;

    // Create an assignment to the return of the alloca (the instruction) from a
    // the stack object
    std::string fact = createAssign(IDMap.saveAndGetID(&I), stackStr);

    writeFact(&I, fact);
  }

  void FactVisitor::visitCallInst(CallInst &I) {
    CallSite ci = CallSite(&I);
    handleCallSite(ci);
  }

  void FactVisitor::visitInvokeInst(InvokeInst &I) {
    CallSite ci = CallSite(&I);
    handleCallSite(ci);
  }

  void FactVisitor::handleCallSite(CallSite I) {
    DEBUG_MSG("Visiting CallSite: " << *(I.getInstruction()) << "\n");
    DEBUG_MSG("\tType? " << *(I.getType()) << '\n');

    // The type returned by the function
    Type *retTy = I.getType();
    Function *callee = I.getCalledFunction();
    assert(callee != NULL && "Calling indirect function");
    if (retTy->isPointerTy()) {
      StringRef funcName = callee->getName();
      assert(funcName.size() && "Calling function without name");

      // Get the ID of the callsite instruction
      Instruction *cs = I.getInstruction();
      //std::string callID = getInstIDStr(saveAndGetInstID(cs), cs);
      //std::string callID = getInstIDStr(saveAndGetID(cs), cs);

      if (isMalloc(callee)) {
        std::string fact = createMalloc(cs);
        (*datalogFile) << getCommentChar() << ' ' << *cs << '\n';
        (*datalogFile) << fact << '\n';
      }
      else {
        // Create an alias link from the return instruction to the return of the
        // function
        // Each function has a node for its return value (see visitReturnInst())
        std::string funcRetName = getFuncReturnName(funcName);
        // Create an assignment to the CallSite (the return) to the return of the
        // function.
        //std::string fact = createAssign(callID, funcRetName);
        std::string fact = createAssign(IDMap.saveAndGetID(cs), funcRetName);
        writeFact(cs, fact);
      }
    }
    DEBUG_MSG("\tHandling callsite arguments\n");

    // If the function has external linkage, we can still view its arguments and
    // setup the alias links
    // Get the IDs and positions of relevant 
    //std::vector<FuncArgPair> args = saveAndGetFuncArgIds(callee);
    for (auto i = callee->arg_begin(), e = callee->arg_end(); i != e; ++i) {
      Argument &a = *i;
      if (!a.getType()->isPointerTy()) {
        continue;
      }

      // Get an ID to the operand used in the caller
      Value *callerOp = I.getArgument(a.getArgNo());
      assert(callerOp && "argument not found on caller");

      // Handle the different types of values which can be used as a call
      // instruction argument
      // This value will be set based on the cases below
      Value *fromOp;
      if (Instruction *inst = dyn_cast<Instruction>(callerOp)) {
        assert(callerOp->getType() == a.getType() 
            && "caller operand does not match func argument type");
        fromOp = callerOp;
      }
      else if (ConstantExpr *ce = dyn_cast<ConstantExpr>(callerOp)) {
        Instruction *asI = ce->getAsInstruction();

        if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(asI)) {
          DEBUG_MSG("\tConstExpr is GEP\n");
          // Have the argument points to the pointer in the GEP.
          // TODO: Optimization:
          // All GEP instructions to the same base pointer are considered to
          // alias
          fromOp = gep->getPointerOperand();
        }
        else {
          errs() << "[ERROR] ConstExpr as Instruction: " << *asI << '\n';
          llvm_unreachable("unhandled ConstExpr type (see above)");
        }
      }
      else {
        errs() << "[ERROR]: Caller Argument Type: " << *callerOp << '\n';
        llvm_unreachable("unhandled caller argument type (see above)");
      }

      assert(fromOp && "fromOp not set at callsite");
      // Link the function argument to the callsite argument
      DEBUG_MSG("\tLinking function arg to callsite arg\n");
      std::string fact = createAssign(&a, fromOp);
      writeFact(I.getInstruction(), fact);
    }

    DEBUG_MSG("Finished callsite\n");
  }

  std::string FactVisitor::createAssign(std::string to, std::string from) {
      std::string ret;
    if (useIntIDs) {
      // Convert the string keys to integers
      to = Utils::to_const_bitvec(IDMap.saveAndGetIntID(to));
      from = Utils::to_const_bitvec(IDMap.saveAndGetIntID(from));
      DEBUG_MSG("create assign: to: " << to << '\n');
    }
    if (datalog) {
      ret = "Assign(\"" + to + "\", \"" + from + "\").";
    }
    else {
      ret = "(rule (assign " + to + ' ' + from + "))";
    }
    assert(ret.size());
    return ret;
  }

  std::string FactVisitor::createAssign(Value *to, Value *from) {
    assert(to != NULL && "NULL Passed");
    assert(from != NULL && "NULL Passed");

    // Attempt to convert to and from to values which are handled
    std::string toStr = IDMap.saveAndGetID(to);
    std::string fromStr = IDMap.saveAndGetID(from);

    return createAssign(toStr, fromStr);
  }

  std::string FactVisitor::createLoad(Value *to, Value *from) {
    assert(to && "NULL Passed");
    assert(from && "NULL Passed");

    assert(from->getType() && "from value with NULL type");
    assert(from->getType()->isPointerTy() && "from value that is not a pointer");
    assert(from->getType()->isPointerTy() && "from value that is not a pointer");
    assert(dyn_cast<PointerType>(from->getType())->getElementType()->isPointerTy()
          && "Creating load from non double pointer");

    std::string toStr = IDMap.saveAndGetID(to);
    // Get the ID of the dereferenced form of the from pointer
    std::string fromStr = IDMap.saveAndGetID(from);


    // Remove one star from the to. This represents it being dereferenced
    // once. That is, in a store instruction, the pointer operand is dereferenced
    // and then assigned.
    //
    // The dereferenced string is not actually a value in the program. It is
    // simply a temporary node in the graph which is used to hook up with
    // subsequent loads. It is not stored in the ValToStrDB and thus will not be
    // found in the module's metadata. After the analysis is done, it can be
    // discarded.
    std::string derefFrom = ValToStrDB::rmStar(fromStr);
    assert(derefFrom[0] == '*' && "underlying type is not a pointer");


    return createAssign(toStr, derefFrom + "_tmp");
  }


  std::string FactVisitor::createStore(Value *to, Value *from) {
    assert(to && "NULL passed");
    assert(from && "NULL passed");

    assert(to->getType() && "to value with NULL type");
    assert(to->getType()->isPointerTy() && "to value that is not a pointer");
    assert(to->getType()->isPointerTy() && "to value that is not a pointer");

    // Currently only support storing to some types:
    // Storing an {instruction, function argument, global variable} in a
    // {global, instruction}
    if (!((isa<Instruction>(from) 
            || isa<Argument>(from)
            || isa<GlobalVariable>(from)) 
      && 
        (isa<Instruction>(to)
         || isa<GlobalVariable>(to)))) {
      DEBUG_MSG("[ERROR] Value Operand: " << *from << "\n\tPointer Operand: " 
          << *to << '\n');
      llvm_unreachable("unhandled store types (see above)");
    }

    DEBUG_MSG("createStore():\n\tto: " << *to << '\n');

    std::string toStr = IDMap.saveAndGetID(to);
    DEBUG_MSG("\ttoStr: " << toStr << '\n');
    // Get the ID of the dereferenced form of the from pointer
    std::string fromStr = IDMap.saveAndGetID(from);

    // Remove one star from the value being stored(i.e., the pointer operand).
    // This represents it being dereferenced once.
    //
    // The dereferenced string is not actually a value in the program. It is
    // simply a temporary node in the graph which is used to hook up with
    // subsequent loads. It is not stored in the ValToStrDB and thus will not be
    // found in the module's metadata. After the analysis is done, it can be
    // discarded.
    std::string derefTo = ValToStrDB::rmStar(toStr);
    assert(derefTo[0] == '*' && "underlying type is not a pointer");


    // Assigning to the derefenced pointer the value operand
    return createAssign(derefTo + "_tmp", fromStr);

  }

  std::string FactVisitor::createMalloc(Value *to) {
    assert(to != NULL && "NULL passed");

    // Every malloc call is considered to create a distinct heap object
    static uint64_t ID = 0;

    std::string heapStr = "heap_" + std::to_string(ID);
    std::string toStr = IDMap.saveAndGetID(to);
    std::string ret;

    if (this->onlyMalloc) {
      ret = "AllocHeap(\"" + toStr + "\", \"" + heapStr + "\").";
    }
    else {
      ret = createAssign(toStr, heapStr);
    }

    // Increment the ID so the next time this function is called it creates a
    // distinct heap object
    ID += 1;
    assert(ret.size() && "createMalloc(): returning empty string");

    return ret;
  }

  bool FactVisitor::isMalloc(Function *f) {
    StringRef fn = f->getName();
    if (fn.equals("malloc")) {
      DEBUG_MSG("Malloc found\n");
      return true;
    }
    else {
      return false;
    }
  }

  char FactVisitor::getCommentChar() {
    if (datalog) {
      return '#';
    }
    else {
      return ';';
    }
  }

  void FactVisitor::writeFact(Value *v, std::string fact) {
    assert(fact.size() && "empty string passed");
    assert(v && "NULL value passed");

    (*datalogFile) << getCommentChar() << ' ' << *v << '\n'
                   << fact << '\n';
  }

  std::string FactVisitor::Constants::getStr(Constant *c) {
    if (isa<ConstantPointerNull>(c)) {
      return NULL_STR;
    }
    else {
      DEBUG_MSG("Constant: " << *c << '\n');
      llvm_unreachable("unhandled constant, see above");
    }
  }

  //void FactVisitor::visitBranchInst(BranchInst &I);
  //void FactVisitor::visitSwitchInst(SwitchInst &I);
  //void FactVisitor::visitIndirectBrInst(IndirectBrInst &I);
  //void FactVisitor::visitResumeInst(ResumeInst &I);
  //void FactVisitor::visitUnreachableInst(UnreachableInst &I);
  //void FactVisitor::visitICmpInst(ICmpInst &I);
  //void FactVisitor::visitFCmpInst(FCmpInst &I);
  //void FactVisitor::visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
  //void FactVisitor::visitAtomicRMWInst(AtomicRMWInst &I);
  //void FactVisitor::visitFenceInst(FenceInst &I);
  //void FactVisitor::visitGetElementPtrInst(GetElementPtrInst &I);
  //void FactVisitor::visitPHINode(PHINode &I);
  //void FactVisitor::visitTruncInst(TruncInst &I);
  //void FactVisitor::visitZExtInst(ZExtInst &I);
  //void FactVisitor::visitSExtInst(SExtInst &I);
  //void FactVisitor::visitFPTruncInst(FPTruncInst &I);
  //void FactVisitor::visitFPExtInst(FPExtInst &I);
  //void FactVisitor::visitFPToUIInst(FPToUIInst &I);
  //void FactVisitor::visitFPToSIInst(FPToSIInst &I);
  //void FactVisitor::visitUIToFPInst(UIToFPInst &I);
  //void FactVisitor::visitSIToFPInst(SIToFPInst &I);
  //void FactVisitor::visitPtrToIntInst(PtrToIntInst &I);
  //void FactVisitor::visitIntToPtrInst(IntToPtrInst &I);
  //void FactVisitor::visitBitCastInst(BitCastInst &I);
  //void FactVisitor::visitAddrSpaceCastInst(AddrSpaceCastInst &I);
  //void FactVisitor::visitSelectInst(SelectInst &I);
  //void FactVisitor::visitVAArgInst(VAArgInst &I);
  //void FactVisitor::visitExtractElementInst(ExtractElementInst &I);
  //void FactVisitor::visitInsertElementInst(InsertElementInst &I);
  //void FactVisitor::visitShuffleVectorInst(ShuffleVectorInst &I);
  //void FactVisitor::visitExtractValueInst(ExtractValueInst &I);
  //void FactVisitor::visitInsertValueInst(InsertValueInst &I);
  //void FactVisitor::visitLandingPadInst(LandingPadInst &I);
  //void FactVisitor::visitDbgDeclareInst(DbgDeclareInst &I);
  //void FactVisitor::visitDbgValueInst(DbgValueInst &I);
  //void FactVisitor::visitDbgInfoIntrinsic(DbgInfoIntrinsic &I);
  //void FactVisitor::visitMemSetInst(MemSetInst &I);
  //void FactVisitor::visitMemCpyInst(MemCpyInst &I);
  //void FactVisitor::visitMemMoveInst(MemMoveInst &I);
  //void FactVisitor::visitMemTransferInst(MemTransferInst &I);
  //void FactVisitor::visitMemIntrinsic(MemIntrinsic &I);
  //void FactVisitor::visitVAStartInst(VAStartInst &I);
  //void FactVisitor::visitVAEndInst(VAEndInst &I);
  //void FactVisitor::visitVACopyInst(VACopyInst &I);
  //void FactVisitor::visitIntrinsicInst(IntrinsicInst &I);
} // namespace ciaa
