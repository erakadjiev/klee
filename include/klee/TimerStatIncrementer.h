//===-- TimerStatIncrementer.h ----------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_TIMERSTATINCREMENTER_H
#define KLEE_TIMERSTATINCREMENTER_H

#include "klee/InstructionContext.h"
#include "klee/Statistics.h"
#include "klee/Internal/Support/Timer.h"

namespace klee {
  class TimerStatIncrementer {
  private:
    WallTimer timer;
    Statistic &statistic;
    InstructionContext& instrCtx;

  public:
    TimerStatIncrementer(Statistic &_statistic) : statistic(_statistic), instrCtx(InstructionContext::emptyContext()) {}
    TimerStatIncrementer(Statistic &_statistic, InstructionContext& instrCtx) : statistic(_statistic), instrCtx(instrCtx) {}
    ~TimerStatIncrementer() {
      statistic.add(timer.check(), instrCtx); 
    }

    uint64_t check() { return timer.check(); }
  };
}

#endif
