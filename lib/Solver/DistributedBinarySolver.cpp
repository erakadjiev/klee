//===-- DistributedBinarySolver.cpp ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include <string>
#include "klee/TimerStatIncrementer.h"

#include "Serializer.h"
#include "MetaSMTDeserializer.h"

#include "klee/util/ExprSMTLIBPrinter.h"

#include <metaSMT/frontend/Array.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/support/run_algorithm.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Group.hpp>

#define Expr VCExpr
#define STP STP_Backend
#include <metaSMT/backend/STP.hpp>
#undef Expr
#undef STP

#include <metaSMT/DirectSolver_Context.hpp>

//for findSymbolicObjects()
#include "klee/util/ExprUtil.h"

#include "klee/util/Assignment.h"
#include "../Core/Common.h"

#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

//remove me
#include <iostream>
#include <cstdio>

#include <errno.h>

#include "SolverStats.h"

namespace klee {
  class DistributedBinarySolverImpl: public SolverImpl {
    private:

      double timeout;

      SolverRunStatus _runStatusCode;

      metaSMT::DirectSolver_Context<metaSMT::solver::STP_Backend> metaSmtSolver;
      
      Serializer* serializer;
      MetaSMTDeserializer<metaSMT::DirectSolver_Context<metaSMT::solver::STP_Backend>>* deserializer;

      unsigned int queryNum;
      std::string error;
      llvm::raw_fd_ostream f;
      
      void giveUp();

      virtual SolverImpl::SolverRunStatus solveRemotely(const Query& q,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values,
          bool& hasSolution);

    public:
      DistributedBinarySolverImpl(const std::string _solverAddress);
      ~DistributedBinarySolverImpl();

      ///Set the time in seconds to wait for the solver to complete.
      ///This time is rounded to the nearest second.
      ///The default is 0 (i.e. no timeout)
      void setCoreSolverTimeout(double _timeout);

      char* getConstraintLog(const Query&);

      bool computeTruth(const Query&, bool& isValid);
      bool computeValue(const Query&, ref<Expr>& result);
      bool computeInitialValues(const Query&,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values, bool& hasSolution);

      SolverImpl::SolverRunStatus getOperationStatusCode();
  };
  
  DistributedBinarySolver::DistributedBinarySolver(std::string solverAddress) :
          Solver(new DistributedBinarySolverImpl(solverAddress)) {
  }
  
  DistributedBinarySolver::~DistributedBinarySolver(){
  }

  void DistributedBinarySolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  char* DistributedBinarySolver::getConstraintLog(const Query& query) {
    return (impl->getConstraintLog(query));
  }

  // ------------------------------------- DistributedBinarySolverImpl methods ----------------------------------------
  
  DistributedBinarySolverImpl::DistributedBinarySolverImpl(const std::string _solverAddress) :
          timeout(0.0), _runStatusCode(SOLVER_RUN_STATUS_FAILURE), metaSmtSolver(), serializer(new Serializer()), 
          deserializer(new MetaSMTDeserializer<metaSMT::DirectSolver_Context<metaSMT::solver::STP_Backend>>(metaSmtSolver, true, true)), queryNum(0), f("/home/rakadjiev/Desktop/capnp.smt2", error, llvm::raw_fd_ostream::F_Binary) {}

  DistributedBinarySolverImpl::~DistributedBinarySolverImpl() {
    delete serializer;
    delete deserializer;
  }

  void DistributedBinarySolverImpl::giveUp() {
//    klee_error("DistributedBinarySolverImpl: Giving up!");
  }
  
  void DistributedBinarySolverImpl::setCoreSolverTimeout(double _timeout) {
    timeout = _timeout;
  }
  
  char* DistributedBinarySolverImpl::getConstraintLog(const Query& q) {
    const char* msg = "Not supported";
    char *buf = new char[strlen(msg) + 1];
    strcpy(buf, msg);
    return(buf);
  }
  
  bool DistributedBinarySolverImpl::computeTruth(const Query& query, bool& isValid) {
    bool success = false;
    std::vector<const Array*> objects;
    std::vector<std::vector<unsigned char> > values;
    bool hasSolution;
    
    if (computeInitialValues(query, objects, values, hasSolution)) {
      // query.expr is valid iff !query.expr is not satisfiable
      isValid = !hasSolution;
      success = true;
    }
    
    return (success);
  }
  
  bool DistributedBinarySolverImpl::computeValue(const Query& query, ref<Expr>& result) {
    
    bool success = false;
    std::vector<const Array*> objects;
    std::vector<std::vector<unsigned char> > values;
    bool hasSolution;
    
    // Find the object used in the expression, and compute an assignment for them.
    findSymbolicObjects(query.expr, objects);
    
    if (computeInitialValues(query.withFalse(), objects, values, hasSolution)) {
      assert(hasSolution && "state has invalid constraint set");
      // Evaluate the expression with the computed assignment.
//      for(int i = 0; i < values.size(); ++i){
//        for(int j = 0; j < values[i].size(); ++j){
//          std::cerr << (int)(values[i][j]) << " ";
//        }
//        std::cerr << "\n";
//      }
      
     //std::cerr << "[";
//      int i = 0;
//      for(std::vector<const Array*>::const_iterator it = objects.begin(), ie = objects.end(); it != ie; ++it){
//        for(int j = 0; j < (*it)->size; ++j){
//          //        std::cerr << (int)(values[i][j]) << " ";
//          unsigned char* c = (unsigned char*) & (values[i][j]);
//          for (int k = 0; k < sizeof (double); ++k) {
//            printf ("%02X ", c[i]);
//          }
//          printf (" ");
//        }
//        
//        ++i;
//      }
     //std::cerr << "]\n";
      Assignment a(objects, values);
      result = a.evaluate(query.expr);
//      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(result)){
//       //std::cerr << "Result: " << CE->getWidth() << " " << CE->isTrue() << " " << CE->getZExtValue() << "\n";
//      } else {
//       //std::cerr << "Result not constant\n";
//      }
      
      success = true;
    }
    
    return (success);
  }
  
  bool DistributedBinarySolverImpl::computeInitialValues(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values, bool& hasSolution) {
    
    ++queryNum;
    
    _runStatusCode = SOLVER_RUN_STATUS_FAILURE;
    
    TimerStatIncrementer t(stats::queryTime);
    
//    ExprSMTLIBPrinter p;
//    p.setHumanReadable(true);
//    f << "{Query " << queryNum << "}\n";
//    p.setOutput(f);
//    p.setQuery(query);
//    p.setArrayValuesToGet(objects);
//    p.generateOutput();
//    llvm::errs().flush();
    
    ++stats::queries;
    ++stats::queryCounterexamples;
    
    _runStatusCode = solveRemotely(query, objects, values, hasSolution);
    bool success = ((SOLVER_RUN_STATUS_SUCCESS_SOLVABLE == _runStatusCode)
        || (SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE == _runStatusCode));
    
//    assert(objects.size() == values.size() && "The number of counterexamples doesn't equal the number of requested assignments.");
//    int i = 0;
//    for(std::vector<const Array*>::const_iterator it = objects.begin(), ie = objects.end(); it != ie; ++it){
//      assert((*it)->size == values[i].size() && "The size of one of the counterexamples doesn't equal the size of the requested assignments.");
//      ++ i;
//    }
    
//    p.setQuery(query);
//    p.setArrayValuesToGet(objects);
//    p.generateOutput();
//    llvm::errs().flush();
    
   //std::cerr << "Query " << queryNum << ": ";
    if (success) {
      if (hasSolution) {
       //std::cerr << "sat\n";
        ++stats::queriesInvalid;
      } else {
       //std::cerr << "unsat\n";
        ++stats::queriesValid;
      }
    } else {
       //std::cerr << "unknown\n";
    }
    
    return success;
  }

  SolverImpl::SolverRunStatus DistributedBinarySolverImpl::solveRemotely(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values,
      bool& hasSolution) {

    capnp::MallocMessageBuilder queryMsg;
    capnp::MessageBuilder&& queryMsgFilled = serializer->serialize(query, objects, std::move(queryMsg));
    capnp::MallocMessageBuilder replyMsg;
    capnp::MessageBuilder&& replyMsgFilled = static_cast<capnp::MallocMessageBuilder&&>(deserializer->deserializeAndSolve(queryMsgFilled.getSegmentsForOutput(), std::move(replyMsg)));
    capnp::SegmentArrayMessageReader message(replyMsgFilled.getSegmentsForOutput());
    
    serialization::Reply::Reader reply = message.getRoot<serialization::Reply>();
    
    SolverImpl::SolverRunStatus ret;
    if(reply.isSat()){
      hasSolution = true;
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
      
      serialization::Reply::Sat::Reader sat = reply.getSat();
      if(sat.isAssignments()){
        capnp::List<capnp::List<uint8_t>>::Reader assignments = sat.getAssignments();
        unsigned assignmentsSize = assignments.size();
        assert(assignmentsSize == objects.size() && "The number of computed assignments does not equal the number of requested assignments.");
        values.reserve(assignmentsSize);
        for(unsigned i = 0; i < assignmentsSize; ++i){
          capnp::List<uint8_t>::Reader assignment = assignments[i];
          unsigned assignmentSize = assignment.size();
          assert((assignmentSize == objects[i]->size) && "The size of one of the computed assignments does not equal the size of the original array.");
          std::vector<unsigned char> data;      
          data.reserve(assignmentSize);
          for(unsigned j = 0; j < assignmentSize; ++j){
            unsigned char a = (unsigned char)(((unsigned)'0')+assignment[j]);
            data.push_back(a);
          }
          values.push_back(data);
        }
      }
    } else if (reply.isUnsat()){
      hasSolution = false;
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
    } else {
      hasSolution = false;
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_FAILURE;
    }
    
    return ret;
  }

  SolverImpl::SolverRunStatus DistributedBinarySolverImpl::getOperationStatusCode() {
    return _runStatusCode;
  }

}
