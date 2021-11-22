/*
 *
 * Author: Markus Kusano
 *
 * Context insensitive intraprocedural alias analysis. 
 *
 * The output datalog file will be the module name with ".datalog" appended.
 *
 * This pass is a frontend to create a datalog database of relevant relations
 * in the program. The output is a datalog file which can be passed to a
 * datalog engine to calculate the points-to relation
 *
 * There are two specifications availible. They can be toggled with the
 * -only-malloc option
 *
 * The default behavior (only-malloc is false) is to consider all pointer
 * relationships regardless of if they trace back to a malloc call:
 *
 * # Assignment
 * Assign(to, from)
 *
 * # A variable pointing to memory location
 * PointsTo(var, loc) print tuples
 *
 * PointsTo(var, heap) :- Assign(var, heap).
 *
 * # Find the transitive closure of pointer assignments
 * PointsTo(to, heap) :- Assign(to, from), PointsTo(from, heap).
 *
 * It is simply the transitive closure of all pointer assignments.
 *
 * If -only-malloc is specified, then only assignments which can transitively
 * reach a malloc call are considered to be in the points-to relation.
 *
 * # Heap allocation
 * AllocHeap(var, heap)
 *
 * # Assignememt
 * Assign(to, from)
 *
 * # An item is in the PointsTo relation if it is a heap allocation
 * PointsTo(var, heap) :- AllocHeap(var, heap)
 *
 * # Or, if it can transitively reach a heap allocation
 * PointsTo(to, heap) :- Assign(to, from), PointsTo(from, heap).
 *
 * Note that -only-malloc ignores shared globals unless they are malloc()ed
 *
 * If the option -datalog is passed, then the output file will be in the
 * datalog format.
 *
 * Otherwise, it will be in the SMTLIB-2 format (with Microsoft extensions for
 * fix points). See http://rise4fun.com/Z3/tutorialcontent/fixedpoints
 */

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "FactVisitor.h"

#include <string>

using namespace llvm;

// Remove this macro definition to disable debugging output to stderr
#define MK_DEBUG
#include "utils/mk_debug.h"


static cl::opt<bool> 
    onlyMalloc("only-malloc", 
	cl::desc("Only consider points-to relations which can trace back to malloc"),
	cl::init(false));

static cl::opt<bool> 
    datalog("datalog", 
	cl::desc("Output in datalog format"),
	cl::init(false));


struct aliasAnaly : public ModulePass {
  static char ID;

  aliasAnaly() : ModulePass(ID) { }

  // Append the specification to the top of the file. Uses onlyMalloc
  // global to determine which spec to append.
  void addSpec(raw_fd_ostream &f) {
    if (datalog) {
      // TODO: Is this in bits or number of possible values?
      f << "Z 65536\n";
      // Regardless of onlyMalloc, assignment and pointsTo have the same type
      // definition
      f << "\n" << "Assign(to : Z, from : Z)\n";
      f << "PointsTo(var : Z, loc : Z) printtuples\n";

      if (onlyMalloc) {
        // onlyMalloc includes a special heap allocation relation
        f << "# only tracing back to malloc calls\n"
          << "AllocHeap(var : Z, heap : Z)\n\n";
        // Points-to relations for only tracing back to malloc'ed values
        f << "# An item is in the PointsTo relation if it is a heap allocation\n"
          << "PointsTo(var, heap) :- AllocHeap(var, heap).\n"
          << "\n# Or, if it can transitively reach a heap allocation\n"
          << "PointsTo(to, heap) :- Assign(to, from), PointsTo(from, heap).\n\n";
      }
      else {
        f << "# A pointer points to what it is assigned to\n"
          << "PointsTo(var, heap) :- Assign(var, heap).\n"
          << "\n# A pointer points to the transitive closure of its assignments\n"
          << "PointsTo(to, heap) :- Assign(to, from), PointsTo(from, heap).\n\n";
      }
    }
    // Use SMT-Lib
    else {
      std::string unsigned_size_bits = std::to_string(sizeof(unsigned) * 8);
      f << "(set-option :fixedpoint.engine datalog)\n"
        << "; This sort is used to define all relations. It is the size of an "
        << "unsigned on the target machine.\n"
        << "(define-sort s () (_ BitVec " << unsigned_size_bits << "))\n"
        << "\n"
        << "; Assignment (assign from to)\n"
        << "(declare-rel assign (s s))\n"
        << "; (PointsTo var location)\n"
        << "(declare-rel points-to (s s))\n"
        << '\n'
        << "(declare-var var s)\n"
        << "(declare-var heap s)\n"
        << "(declare-var to s)\n"
        << "(declare-var from s)\n"
        << '\n';
      if (onlyMalloc) {
        // onlyMalloc includes a special heap allocation relation
        f << "; only tracing back to malloc calls\n"
          << "(declare-rel alloc-heap (s, s))\n\n";
        // Points-to relations for only tracing back to malloc'ed values
        f << "; An item is in the PointsTo relation if it is a heap allocation\n"
          << "(rule (=> (alloc-heap var heap) (points-to var heap)))\n"
          //<< "PointsTo(var, heap) <- AllocHeap(var, heap).\n"
          << "\n; Or, if it can transitively reach a heap allocation\n"
          << "(rule (=> (and (assign to from) (points-to from heap)) (points-to to heap)))\n"
          << '\n';
          //<< "PointsTo(to, heap) <- Assign(to, from), PointsTo(from, heap).\n";
      }
      else {
        f << "; A pointer points to what it is assigned to\n"
          << "(rule (=> (assign var heap) (points-to var heap)))\n"
          << "\n; A pointer points to the transitive closure of its assignments\n"
          << "(rule (=> (and (assign to from) (points-to from heap)) (points-to to heap)))\n"
          << '\n';
      }
    }
  }


  virtual bool runOnModule(Module &M) {
    DEBUG_MSG_RED("Starting context insensitive alias analysis pass\n");

    // Use the name of the module as the filename
    std::string modName = M.getModuleIdentifier();
    assert(modName.size() && "Module ID has size zero");
    std::string path;
    if (datalog) {
      path = modName + ".datalog";
    }
    else {
      path = modName + ".smt2";
    }
    assert(path.size() && "empty output file path");

    // Attempt to open a stream to the passed path, crash on failure.
    std::error_code ec;
    // Open file in text mode
    raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec
        , sys::fs::OpenFlags::F_Text);
    if (ec.value()) {
      errs() << "[ERROR] Unable to open file " << path << ": " << ec.message()
             << '\n';
      exit(EXIT_FAILURE);
    }

    // Prepend the specification to the datalog file
    addSpec(*outFile);


    // All facts are populated in the file by the InstVisitor
    // (FactVisitor).
    ciaa::FactVisitor fv(onlyMalloc, datalog, outFile);
    fv.visit(M);

    // Store all the database IDs to the module
    fv.IDMap.dumpIDMapToModule(M);

    // TODO: This is just here to test parsing of IDMap
    std::map<Value *, std::string> idMap = fv.IDMap.parseIDMapFromModule(M);
    assert(ValToStrDB::idMapEqual(idMap, fv.IDMap.IDMap) && "Parsed map differs from IDMap");

    // Add a comment indicating the end of the facts.
    if (datalog) {
      (*outFile) << "#### End facts\n";
    }
    else {
      (*outFile) << ";#### End facts\n";
    }
    outFile->close();

    delete outFile;
    // IR was not modified
    return false;
  }


}; // struct aliasAnaly


char aliasAnaly::ID = 0;
static RegisterPass<aliasAnaly> X("contextinsen-aa",
              "Datalog based frontend for context insensitive alias analysis",
              false,  // unmodified CFG
              true); // analysis pass
