/*
 * InstructionContext.h
 *
 *  Created on: Mar 13, 2015
 *      Author: rakadjiev
 */

#ifndef KLEE_INSTRUCTIONCONTEXT_H_
#define KLEE_INSTRUCTIONCONTEXT_H_

#include <set>

namespace klee{
  class ExecutionState;
  class StatisticRecord;
  
  /// \todo Add a context object to keep track of data only live
  /// during an instruction step. Should contain addedStates,
  /// removedStates, and haltExecution, among others.
  class InstructionContext{
    public:
      InstructionContext(): addedStates(), removedStates(), statsRecord(0), statsIndex(0){}
      /// Used to track states that have been added during the current
      /// instructions step.
      /// \invariant \ref addedStates is a subset of \ref states.
      /// \invariant \ref addedStates and \ref removedStates are disjoint.
      std::set<ExecutionState*> addedStates;
      /// Used to track states that have been removed during the current
      /// instructions step.
      /// \invariant \ref removedStates is a subset of \ref states.
      /// \invariant \ref addedStates and \ref removedStates are disjoint.
      std::set<ExecutionState*> removedStates;
      StatisticRecord* statsRecord;
      unsigned statsIndex;
      
      static InstructionContext& emptyContext(){
        static InstructionContext dummy;
        return dummy;
      }
  };
}


#endif /* KLEE_INSTRUCTIONCONTEXT_H_ */
