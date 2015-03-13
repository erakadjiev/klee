//===-- Statistics.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Statistics.h"

#include <vector>

using namespace klee;

StatisticManager::StatisticManager()
  : enabled(true),
    globalStats(0),
    indexedStats(0) {
}

StatisticManager::~StatisticManager() {
  if (globalStats) delete[] globalStats;
  if (indexedStats) delete[] indexedStats;
}

void StatisticManager::useIndexedStats(unsigned totalIndices) {  
  if (indexedStats) delete[] indexedStats;
  indexedStats = new uint64_t[totalIndices * stats.size()];
  memset(indexedStats, 0, sizeof(*indexedStats) * totalIndices * stats.size());
}

void StatisticManager::registerStatistic(Statistic &s) {
  if (globalStats) delete[] globalStats;
  s.id = stats.size();
  stats.push_back(&s);
  globalStats = new uint64_t[stats.size()];
  memset(globalStats, 0, sizeof(*globalStats)*stats.size());
}

int StatisticManager::getStatisticID(const std::string &name) const {
  for (unsigned i=0; i<stats.size(); i++)
    if (stats[i]->getName() == name)
      return i;
  return -1;
}

Statistic *StatisticManager::getStatisticByName(const std::string &name) const {
  for (unsigned i=0; i<stats.size(); i++)
    if (stats[i]->getName() == name)
      return stats[i];
  return 0;
}

StatisticManager *klee::theStatisticManager = 0;

static StatisticManager &getStatisticManager() {
  static StatisticManager sm;
  theStatisticManager = &sm;
  return sm;
}

/* *** */

Statistic::Statistic(const std::string &_name, 
                     const std::string &_shortName) 
  : name(_name), 
    shortName(_shortName) {
  getStatisticManager().registerStatistic(*this);
}

Statistic::~Statistic() {
}

Statistic &Statistic::add(const uint64_t addend) {
  theStatisticManager->incrementStatistic(*this, InstructionContext::emptyContext(), addend);
  return *this;
}

Statistic &Statistic::add(const uint64_t addend, InstructionContext& instrCtx) {
  theStatisticManager->incrementStatistic(*this, instrCtx, addend);
  return *this;
}

uint64_t Statistic::getValue() const {
  return theStatisticManager->getValue(*this);
}
