//===-- Searcher.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SEARCHER_H
#define KLEE_SEARCHER_H

#include "llvm/Support/raw_ostream.h"
#include <vector>
#include <set>
#include <map>
#include <queue>
#include <unordered_set>

namespace llvm {
  class BasicBlock;
  class Function;
  class Instruction;
  class raw_ostream;
}

namespace klee {
  template<class T> class DiscretePDF;
  class ExecutionState;
  class Executor;
  class CurrentInstructionContext;

  class Searcher {
  public:
    virtual ~Searcher();

    // xxx CurrentInstructionContext reference needed, because some searchers
    // (merging ones) terminate states inside this method
    virtual ExecutionState &selectState(CurrentInstructionContext& instrCtx) = 0;

    virtual void update(ExecutionState *current,
                        const std::set<ExecutionState*> &addedStates,
                        const std::set<ExecutionState*> &removedStates) = 0;

    virtual bool empty() = 0;

    // prints name of searcher as a klee_message()
    // TODO: could probably make prettier or more flexible
    virtual void printName(llvm::raw_ostream &os) {
      os << "<unnamed searcher>\n";
    }

    // pgbovine - to be called when a searcher gets activated and
    // deactivated, say, by a higher-level searcher; most searchers
    // don't need this functionality, so don't have to override.
    virtual void activate() {}
    virtual void deactivate() {}

    // utility functions

    virtual void addState(ExecutionState *es) = 0; // {
//      std::set<ExecutionState*> tmp;
//      tmp.insert(es);
//      update(current, tmp, std::set<ExecutionState*>());
//    }

    virtual void removeState(ExecutionState *es) = 0; // {
//      std::set<ExecutionState*> tmp;
//      tmp.insert(es);
//      update(current, std::set<ExecutionState*>(), tmp);
//    }

    virtual void addStates(const std::set<ExecutionState*> &addedStates){
      for (std::set<ExecutionState*>::const_iterator it = addedStates.begin(),
               ie = addedStates.end(); it != ie; ++it) {
        addState(*it);
      }
    }

    virtual void removeStates(const std::set<ExecutionState*> &removedStates){
      for (std::set<ExecutionState*>::const_iterator it = removedStates.begin(),
               ie = removedStates.end(); it != ie; ++it) {
        removeState(*it);
      }
    }

    enum CoreSearchType {
      DFS,
      BFS,
      RandomState,
      RandomPath,
      ConcurrentRandomPath,
      NURS_CovNew,
      NURS_MD2U,
      NURS_Depth,
      NURS_ICnt,
      NURS_CPICnt,
      NURS_QC
    };
  };

  class DFSSearcher : public Searcher {
    std::vector<ExecutionState*> states;

  public:
    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return states.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "DFSSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class BFSSearcher : public Searcher {
    std::deque<ExecutionState*> states;

  public:
    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return states.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "BFSSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class RandomSearcher : public Searcher {
    std::vector<ExecutionState*> states;

  public:
    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return states.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "RandomSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class WeightedRandomSearcher : public Searcher {
  public:
    enum WeightType {
      Depth,
      QueryCost,
      InstCount,
      CPInstCount,
      MinDistToUncovered,
      CoveringNew
    };

  private:
    DiscretePDF<ExecutionState*> *states;
    WeightType type;
    bool updateWeights;
    
    double getWeight(ExecutionState*);

  public:
    WeightedRandomSearcher(WeightType type);
    ~WeightedRandomSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty();
    void printName(llvm::raw_ostream &os) {
      os << "WeightedRandomSearcher::";
      switch(type) {
      case Depth              : os << "Depth\n"; return;
      case QueryCost          : os << "QueryCost\n"; return;
      case InstCount          : os << "InstCount\n"; return;
      case CPInstCount        : os << "CPInstCount\n"; return;
      case MinDistToUncovered : os << "MinDistToUncovered\n"; return;
      case CoveringNew        : os << "CoveringNew\n"; return;
      default                 : os << "<unknown type>\n"; return;
      }
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class RandomPathSearcher : public Searcher {
    Executor &executor;

  public:
    RandomPathSearcher(Executor &_executor);
    ~RandomPathSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty();
    void printName(llvm::raw_ostream &os) {
      os << "RandomPathSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class ConcurrentRandomPathSearcher : public Searcher {
    Executor &executor;

  public:
    ConcurrentRandomPathSearcher(Executor &_executor);
    ~ConcurrentRandomPathSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty();
    void printName(llvm::raw_ostream &os) {
      os << "ConcurrentRandomPathSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class StateRemovingSearcher : public Searcher {
    Searcher* baseSearcher;

    public:
      StateRemovingSearcher(Searcher* baseSearcher);
      ~StateRemovingSearcher();
      ExecutionState &selectState(CurrentInstructionContext& instrCtx);
      void update(ExecutionState *current,
          const std::set<ExecutionState*> &addedStates,
          const std::set<ExecutionState*> &removedStates);
      bool empty() { return baseSearcher->empty(); }
      void printName(llvm::raw_ostream &os) {
        os << "StateRemovingSearcher containing:\n";
        baseSearcher->printName(os);
      }
      virtual void addState(ExecutionState *es);
      virtual void removeState(ExecutionState *es);
  };

  class MergingSearcher : public Searcher {
    Executor &executor;
    std::set<ExecutionState*> statesAtMerge;
    Searcher *baseSearcher;
    llvm::Function *mergeFunction;

  private:
    llvm::Instruction *getMergePoint(ExecutionState &es);

  public:
    MergingSearcher(Executor &executor, Searcher *baseSearcher);
    ~MergingSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && statesAtMerge.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "MergingSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class BumpMergingSearcher : public Searcher {
    Executor &executor;
    std::map<llvm::Instruction*, ExecutionState*> statesAtMerge;
    Searcher *baseSearcher;
    llvm::Function *mergeFunction;

  private:
    llvm::Instruction *getMergePoint(ExecutionState &es);

  public:
    BumpMergingSearcher(Executor &executor, Searcher *baseSearcher);
    ~BumpMergingSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && statesAtMerge.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "BumpMergingSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class BatchingSearcher : public Searcher {
    Searcher *baseSearcher;
    double timeBudget;
    unsigned instructionBudget;

    ExecutionState *lastState;
    double lastStartTime;
    unsigned lastStartInstructions;

  public:
    BatchingSearcher(Searcher *baseSearcher, 
                     double _timeBudget,
                     unsigned _instructionBudget);
    ~BatchingSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "<BatchingSearcher> timeBudget: " << timeBudget
         << ", instructionBudget: " << instructionBudget
         << ", baseSearcher:\n";
      baseSearcher->printName(os);
      os << "</BatchingSearcher>\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class IterativeDeepeningTimeSearcher : public Searcher {
    Searcher *baseSearcher;
    double time, startTime;
    std::set<ExecutionState*> pausedStates;

  public:
    IterativeDeepeningTimeSearcher(Searcher *baseSearcher);
    ~IterativeDeepeningTimeSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return baseSearcher->empty() && pausedStates.empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "IterativeDeepeningTimeSearcher\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

  class InterleavedSearcher : public Searcher {
    typedef std::vector<Searcher*> searchers_ty;

    searchers_ty searchers;
    unsigned index;

  public:
    explicit InterleavedSearcher(const searchers_ty &_searchers);
    ~InterleavedSearcher();

    ExecutionState &selectState(CurrentInstructionContext& instrCtx);
    void update(ExecutionState *current,
                const std::set<ExecutionState*> &addedStates,
                const std::set<ExecutionState*> &removedStates);
    bool empty() { return searchers[0]->empty(); }
    void printName(llvm::raw_ostream &os) {
      os << "<InterleavedSearcher> containing "
         << searchers.size() << " searchers:\n";
      for (searchers_ty::iterator it = searchers.begin(), ie = searchers.end();
           it != ie; ++it)
        (*it)->printName(os);
      os << "</InterleavedSearcher>\n";
    }
    virtual void addState(ExecutionState *es);
    virtual void removeState(ExecutionState *es);
  };

}

#endif
