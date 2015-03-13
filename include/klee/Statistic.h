//===-- Statistic.h ---------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_STATISTIC_H
#define KLEE_STATISTIC_H

#include "klee/InstructionContext.h"
#include "klee/Config/Version.h"
#include "llvm/Support/DataTypes.h"
#include <string>

namespace klee {
  class Statistic;
  class StatisticManager;
  class StatisticRecord;

  /// Statistic - A named statistic instance.
  ///
  /// The Statistic class holds information about the statistic, but
  /// not the actual values. Values are managed by the global
  /// StatisticManager to enable transparent support for instruction
  /// level and call path level statistics.
  class Statistic {
    friend class StatisticManager;
    friend class StatisticRecord;

  private:
    unsigned id;
    const std::string name;
    const std::string shortName;

  public:
    Statistic(const std::string &_name, 
              const std::string &_shortName);
    ~Statistic();

    /// getID - Get the unique statistic ID.
    unsigned getID() { return id; }

    /// getName - Get the statistic name.
    const std::string &getName() const { return name; }

    /// getShortName - Get the "short" statistic name, used in
    /// callgrind output for example.
    const std::string &getShortName() const { return shortName; }

    /// getValue - Get the current primary statistic value.
    uint64_t getValue() const;

    /// operator uint64_t - Get the current primary statistic value.
    operator uint64_t () const { return getValue(); }

    /// operator++ - Increment the statistic by 1.
    /// This increment method must be called on statistics that have to be kept
    /// track of at instruction level. Those are the ones stored in the call path 
    /// nodes, and are used for calltree tracking. 
    /// E.g. forks, solverTime, instructions. 
    Statistic& increment(InstructionContext& instrCtx) { return add(1, instrCtx); }
    /// Increment the statistic by 1.
    /// Statistic will not be updated on the instruction level (inside the call path node).
    Statistic& increment() { return add(1, InstructionContext::emptyContext()); }
    /// operator++ - Increment the statistic by 1.
    /// Statistic will not be updated on the instruction level (inside the call path node).
    Statistic &operator ++() { return increment(); }

    /// Increment the statistic by \arg addend.
    /// This increment method must be called on statistics that have to be kept
    /// track of at instruction level. Those are the ones stored in the call path 
    /// nodes, and are used for calltree tracking. 
    /// E.g. forks, solverTime, instructions. 
    Statistic& add(const uint64_t addend, InstructionContext& instrCtx);
    /// Increment the statistic by \arg addend.
    /// Statistic will not be updated on the instruction level (inside the call path node).
    Statistic& add(const uint64_t addend);
    /// operator+= - Increment the statistic by \arg addend.
    /// Statistic will not be updated on the instruction level (inside the call path node).
    Statistic &operator +=(const uint64_t addend) { return add(addend); }
  };
}

#endif

