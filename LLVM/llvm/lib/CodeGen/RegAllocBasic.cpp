//===-- RegAllocBasic.cpp - Basic Register Allocator ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the RABasic function pass, which provides a minimal
// implementation of the basic register allocator.
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/Passes.h"
#include "AllocationOrder.h"
#include "LiveDebugVariables.h"
#include "RegAllocBase.h"
#include "Spiller.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include <cstdlib>
#include <queue>
//bobo
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <vector>
#include <iterator>
#include <algorithm>
using namespace llvm;

#define DEBUG_TYPE "regalloc"

static RegisterRegAlloc basicRegAlloc("basic", "basic register allocator",
                                      createBasicRegisterAllocator);

namespace {
  struct CompSpillWeight {
    bool operator()(LiveInterval *A, LiveInterval *B) const {
      return A->weight < B->weight;
    }
  };
}

namespace {
/// RABasic provides a minimal implementation of the basic register allocation
/// algorithm. It prioritizes live virtual registers by spill weight and spills
/// whenever a register is unavailable. This is not practical in production but
/// provides a useful baseline both for measuring other allocators and comparing
/// the speed of the basic algorithm against other styles of allocators.
class RABasic : public MachineFunctionPass, public RegAllocBase
{
  // context
  MachineFunction *MF;

  // state
  std::unique_ptr<Spiller> SpillerInstance;
  std::priority_queue<LiveInterval*, std::vector<LiveInterval*>,
                      CompSpillWeight> Queue;

  // Scratch space.  Allocated here to avoid repeated malloc calls in
  // selectOrSplit().
  BitVector UsableRegs;

public:
  RABasic();

  /// Return the pass name.
  const char* getPassName() const override {
    return "Basic Register Allocator";
  }

  /// RABasic analysis usage.
  void getAnalysisUsage(AnalysisUsage &AU) const override;

  void releaseMemory() override;

  Spiller &spiller() override { return *SpillerInstance; }

  void enqueue(LiveInterval *LI) override {
    Queue.push(LI);
  }

  LiveInterval *dequeue() override {
    if (Queue.empty())
      return nullptr;
    LiveInterval *LI = Queue.top();
    Queue.pop();
    return LI;
  }

  unsigned selectOrSplit(LiveInterval &VirtReg, unsigned last_reg,
                         SmallVectorImpl<unsigned> &SplitVRegs) override;

  /// Perform register allocation.
  bool runOnMachineFunction(MachineFunction &mf) override;
 
  /// init leakVariable
  void leak_init(std::map<unsigned, unsigned> *leakVariable);

  // Helper for spilling all live virtual registers currently unified under preg
  // that interfere with the most recently queried lvr.  Return true if spilling
  // was successful, and append any new spilled/split intervals to splitLVRs.
  bool spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                          SmallVectorImpl<unsigned> &SplitVRegs);

  static char ID;
};

char RABasic::ID = 0;

} // end anonymous namespace

RABasic::RABasic(): MachineFunctionPass(ID) {
  initializeLiveDebugVariablesPass(*PassRegistry::getPassRegistry());
  initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
  initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
  initializeRegisterCoalescerPass(*PassRegistry::getPassRegistry());
  initializeMachineSchedulerPass(*PassRegistry::getPassRegistry());
  initializeLiveStacksPass(*PassRegistry::getPassRegistry());
  initializeMachineDominatorTreePass(*PassRegistry::getPassRegistry());
  initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
  initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
  initializeLiveRegMatrixPass(*PassRegistry::getPassRegistry());
}

void RABasic::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  AU.addRequired<AliasAnalysis>();
  AU.addPreserved<AliasAnalysis>();
  AU.addRequired<LiveIntervals>();
  AU.addPreserved<LiveIntervals>();
  AU.addPreserved<SlotIndexes>();
  AU.addRequired<LiveDebugVariables>();
  AU.addPreserved<LiveDebugVariables>();
  AU.addRequired<LiveStacks>();
  AU.addPreserved<LiveStacks>();
  AU.addRequired<MachineBlockFrequencyInfo>();
  AU.addPreserved<MachineBlockFrequencyInfo>();
  AU.addRequiredID(MachineDominatorsID);
  AU.addPreservedID(MachineDominatorsID);
  AU.addRequired<MachineLoopInfo>();
  AU.addPreserved<MachineLoopInfo>();
  AU.addRequired<VirtRegMap>();
  AU.addPreserved<VirtRegMap>();
  AU.addRequired<LiveRegMatrix>();
  AU.addPreserved<LiveRegMatrix>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

void RABasic::releaseMemory() {
  SpillerInstance.reset();
}


// Spill or split all live virtual registers currently unified under PhysReg
// that interfere with VirtReg. The newly spilled or split live intervals are
// returned by appending them to SplitVRegs.
bool RABasic::spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                                 SmallVectorImpl<unsigned> &SplitVRegs) {
  // Record each interference and determine if all are spillable before mutating
  // either the union or live intervals.
  SmallVector<LiveInterval*, 8> Intfs;

  // Collect interferences assigned to any alias of the physical register.
  for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
    LiveIntervalUnion::Query &Q = Matrix->query(VirtReg, *Units);
    Q.collectInterferingVRegs();
    if (Q.seenUnspillableVReg())
      return false;
    for (unsigned i = Q.interferingVRegs().size(); i; --i) {
      LiveInterval *Intf = Q.interferingVRegs()[i - 1];
      if (!Intf->isSpillable() || Intf->weight > VirtReg.weight)
        return false;
      Intfs.push_back(Intf);
    }
  }
  DEBUG(dbgs() << "spilling " << TRI->getName(PhysReg) <<
        " interferences with " << VirtReg << "\n");
  assert(!Intfs.empty() && "expected interference");

  // Spill each interfering vreg allocated to PhysReg or an alias.
  for (unsigned i = 0, e = Intfs.size(); i != e; ++i) {
    LiveInterval &Spill = *Intfs[i];

    // Skip duplicates.
    if (!VRM->hasPhys(Spill.reg))
      continue;

    // Deallocate the interfering vreg by removing it from the union.
    // A LiveInterval instance may not be in a union during modification!
    Matrix->unassign(Spill);

    // Spill the extracted interval.
    LiveRangeEdit LRE(&Spill, SplitVRegs, *MF, *LIS, VRM);
    spiller().spill(LRE);
  }
  return true;
}

// Add the leak variables before the selectOrSplit function
void RABasic::leak_init(std::map<unsigned, unsigned> *leakVariable)
{
    // by lldb to get the virtual register ID
    // test: %vreg0, %vreg3
    leakVariable->insert(std::pair<unsigned, unsigned>(2147483648, 228));
    leakVariable->insert(std::pair<unsigned, unsigned>(2147483651, 229));
}

// Driver for the register assignment and splitting heuristics.
// Manages iteration over the LiveIntervalUnions.
//
// This is a minimal implementation of register assignment and splitting that
// spills whenever we run out of registers.
//
// selectOrSplit can only be called once per live virtual register. We then do a
// single interference test for each register the correct class until we find an
// available register. So, the number of interference tests in the worst case is
// |vregs| * |machineregs|. And since the number of interference tests is
// minimal, there is no value in caching them outside the scope of
// selectOrSplit().
unsigned RABasic::selectOrSplit(LiveInterval &VirtReg, unsigned last_reg_index,
                                SmallVectorImpl<unsigned> &SplitVRegs) {
  // Populate a list of physical register spill candidates.
  SmallVector<unsigned, 8> PhysRegSpillCands;
  
    /*
  // bobo Pre-allocate the sensitive virtual variables
  std::map<unsigned, unsigned> leakVariable;
  std::map<unsigned, unsigned>::iterator s_it;
  leak_init(&leakVariable);
  //check the virtual reg is in the sensitive list or not
    unsigned leak_reg = VirtReg.reg;
    if(leakVariable.find(leak_reg) != leakVariable.end())
    {
        DEBUG(dbgs() << "leak register is " << leak_reg << "\n");
        s_it = leakVariable.find(leak_reg);
        //firstly consider to spill this leak sensitive variable
        DEBUG(dbgs() << "spilling: " << VirtReg << '\n');
        if (VirtReg.isSpillable())
        {
            LiveRangeEdit LRE(&VirtReg, SplitVRegs, *MF, *LIS, VRM);
            spiller().spill(LRE);
            return 0;
        }else
        {
            // allocate the reserved registers
            return s_it->second;
        }
        // To-Do: when the VirtReg cannot be spilled and there are not enough physical registers to be allocated.
    }
    
   */ 
  // Check for an available register in this class.
  AllocationOrder Order(VirtReg.reg, *VRM, RegClassInfo);
  while (unsigned PhysReg = Order.next()) {
    //the vreg5 doesn't have hint, cz it doesn;t have the copy relation with vreg7(%eax)
    //in order to avoid assigning the same reg %eax to vreg5, write modification on choosing physreg from allocation order.
    unsigned reg_index = TargetRegisterInfo::virtReg2Index(VirtReg.reg);
    
    //bobo
    //newly added
      std::string toCheck = std::to_string(reg_index);
      std::string s;
      std::ifstream fin("forBackend.txt");
      bool continue_flag = false;
      if(!(fin.peek() == std::ifstream::traits_type::eof())) // forbackend file is not empty
      {
          //bobo wrote before
         /*
          while(fin >> s)
          {
        //if(reg_index == 5)
              if(!s.compare(toCheck))
              {
            //bobo => the first version use the next candidate as the allocated phys reg for this VirtReg
            //PhysReg = Order.next();
            unsigned last_physreg;
            unsigned last_reg = TargetRegisterInfo::index2VirtReg(last_reg_index);
            last_physreg = VRM->getPhys(last_reg);
            // print the mapped physical register for the last virtual register
            DEBUG(dbgs() << "the physical register allocated for the last virtual register " << PrintReg(last_physreg, TRI) << '\n');
            if(PhysReg == last_physreg)
                continue;
              }
          }
        */
        //bobo newly added
        while(getline(fin, s))
        {
            std::istringstream iss(s);
            std::vector<std::string> tokens;
            std::copy(std::istream_iterator<std::string>(iss), std::istream_iterator<std::string>(), std::back_inserter(tokens));
            iss.str("");
            iss.clear();
            // HD_SENSITIVE masking
            if(std::find(tokens.begin(), tokens.end(), "HD_SENSITIVE") != tokens.end())
            {
                if(std::find(tokens.begin(), tokens.end(), toCheck) != tokens.end())
                {
                    unsigned last_physreg;
                    unsigned last_reg = TargetRegisterInfo::index2VirtReg(last_reg_index);
                    last_physreg = VRM->getPhys(last_reg);
                    DEBUG(dbgs() << "the physical register allocated for the last virtual register " << PrintReg(last_physreg, TRI) << '\n');
                    if(PhysReg == last_physreg)
                        continue_flag = true;
                    break;
                }
            }else // HD_SENSITIVE_2 masking
            {
                if(std::find(tokens.begin(), tokens.end(), toCheck) != tokens.end())
                {
                    std::string to = tokens[0];
                    unsigned reg_0_index = std::stoi(to);
                    unsigned reg_0 = TargetRegisterInfo::index2VirtReg(reg_0_index);
                    std::string from = tokens[1];
                    unsigned reg_1_index = std::stoi(from);
                    unsigned reg_1 = TargetRegisterInfo::index2VirtReg(reg_1_index);
                    if(VRM->hasPhys(reg_0))
                        // the virtual register(toCheck) must be the reg_1
                    {
                        unsigned reg_0_physreg = VRM->getPhys(reg_0);
                        if(PhysReg == reg_0_physreg)
                        {
                            continue_flag = true;
                            break;
                        }
                        continue;
                    }else if(VRM->hasPhys(reg_1))
                    {
                        // the virtual register(toCheck) must be the reg_1 must be reg_0
                        unsigned reg_1_physreg = VRM->getPhys(reg_1);
                        if(PhysReg == reg_1_physreg)
                        {
                            continue_flag = true;
                            break;
                        }
                        continue;
            
                    }else{
                        // both reg_0 and reg_1 are not distributed
                        continue;
                    }
                }
            }
        }
      }
      
      fin.close();
      if(continue_flag)
          continue;
      //bobo end
      
    // Check for interference in PhysReg
    switch (Matrix->checkInterference(VirtReg, PhysReg)) {
    case LiveRegMatrix::IK_Free:
      // PhysReg is available, allocate it.
      return PhysReg;

    case LiveRegMatrix::IK_VirtReg:
      // Only virtual registers in the way, we may be able to spill them.
      PhysRegSpillCands.push_back(PhysReg);
      continue;

    default:
      // RegMask or RegUnit interference.
      continue;
    }
  }

  // Try to spill another interfering reg with less spill weight.
  for (SmallVectorImpl<unsigned>::iterator PhysRegI = PhysRegSpillCands.begin(),
       PhysRegE = PhysRegSpillCands.end(); PhysRegI != PhysRegE; ++PhysRegI) {
    if (!spillInterferences(VirtReg, *PhysRegI, SplitVRegs))
      continue;

    assert(!Matrix->checkInterference(VirtReg, *PhysRegI) &&
           "Interference after spill.");
    // Tell the caller to allocate to this newly freed physical register.
    return *PhysRegI;
  }

  // No other spill candidates were found, so spill the current VirtReg.
  DEBUG(dbgs() << "spilling: " << VirtReg << '\n');
  if (!VirtReg.isSpillable())
    return ~0u;
  LiveRangeEdit LRE(&VirtReg, SplitVRegs, *MF, *LIS, VRM);
  spiller().spill(LRE);

  // The live virtual register requesting allocation was spilled, so tell
  // the caller not to allocate anything during this round.
  return 0;
}

bool RABasic::runOnMachineFunction(MachineFunction &mf) {
  DEBUG(dbgs() << "********** BASIC REGISTER ALLOCATION **********\n"
               << "********** Function: "
               << mf.getName() << '\n');

  MF = &mf;
  RegAllocBase::init(getAnalysis<VirtRegMap>(),
                     getAnalysis<LiveIntervals>(),
                     getAnalysis<LiveRegMatrix>());

  calculateSpillWeightsAndHints(*LIS, *MF,
                                getAnalysis<MachineLoopInfo>(),
                                getAnalysis<MachineBlockFrequencyInfo>());

  SpillerInstance.reset(createInlineSpiller(*this, *MF, *VRM));

  allocatePhysRegs();

  // Diagnostic output before rewriting
  DEBUG(dbgs() << "Post alloc VirtRegMap:\n" << *VRM << "\n");

  releaseMemory();
  return true;
}

FunctionPass* llvm::createBasicRegisterAllocator()
{
  return new RABasic();
}
