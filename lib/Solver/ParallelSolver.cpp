//===-- ParallelSolver.cpp ------------------------------------------*- C++ -*-===//
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
#include "klee/util/ExprSMTLIBPrinter.h"

//for findSymbolicObjects()
#include "klee/util/ExprUtil.h"

#include "klee/util/Assignment.h"
#include "../Core/Common.h"

//remove me
#include <iostream>

#include <errno.h>

#include "LocalSolverService.h"

#include "SMTLIBOutputLexer.h"

#include "SolverStats.h"

#include <czmq.h>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/future.hpp>
#include <unordered_map>

namespace klee {
  class ParallelSolverImpl: public SolverImpl {
    public:
      class SolverReply{
        public:
        SolverReply() : status(0), reply(nullptr){}
        SolverReply(int status, char* reply) : status(0), reply(reply){}
        bool isEmpty(){
          return (!status && !reply);
        }
        int status;
        char* reply;
      };

    private:

      SMTLIBOutputLexer lexer;

      double timeout;

      SolverRunStatus _runStatusCode;

      ExprSMTLIBPrinter* printer;

      zactor_t* serviceActor;
      zpoller_t* servicePoller;

      std::unordered_map<unsigned int, boost::fibers::promise<SolverReply>> pendingQueries;

      unsigned int reqId;
      const unsigned int maxId = UINT_MAX-1;


      void giveUp();

      static void solver_actor(zsock_t* pipe, void* args);
      std::string& buildSMTLIBv2String(const Query& q,
          const std::vector<const Array*>& arrays, std::string& smtLibString);
      std::string& buildSMTLIBv2String(const Query& q, std::string& smtLibString);
      int generateRequestId();
      SolverReply sendQuery(std::string query);
      virtual SolverImpl::SolverRunStatus solveRemotely(const Query& q,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values,
          bool& hasSolution);
      SolverImpl::SolverRunStatus parseSolverOutput(char* solverOutput,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values,
          bool& hasSolution);

    public:
      ParallelSolverImpl(const std::string _solverAddress);
      ~ParallelSolverImpl();

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
      void waitForResponse();
  };
  
  ParallelSolver::ParallelSolver(std::string solverAddress) :
          Solver(new ParallelSolverImpl(solverAddress)) {
  }
  
  ParallelSolver::~ParallelSolver(){
  }

  void ParallelSolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  char* ParallelSolver::getConstraintLog(const Query& query) {
    return (impl->getConstraintLog(query));
  }

  void ParallelSolver::waitForResponse() {
    static_cast<ParallelSolverImpl*>(impl)->waitForResponse();
  }
  
  // ------------------------------------- ParallelSolverImpl methods ----------------------------------------
  
  ParallelSolverImpl::ParallelSolverImpl(std::string solverAddress) :
          timeout(0.0), _runStatusCode(SOLVER_RUN_STATUS_FAILURE), reqId(0) {
    // FIXME there should be an initial run status code (e.g. _UNKNOWN or _RUNNING)
    printer = new ExprSMTLIBPrinter();
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(false);
    
//    serviceActor = zactor_new(LocalSolverService::solver_actor, (void*)&solverAddress);
    serviceActor = zactor_new(LocalSolverService::solver_actor, NULL);
    servicePoller = zpoller_new(serviceActor, NULL);
    assert(serviceActor);
    assert(servicePoller);

    // CZMQ overrides KLEE's signal handler
    zsys_handler_reset();
  }

  ParallelSolverImpl::~ParallelSolverImpl() {
    zactor_destroy(&serviceActor);
    zpoller_destroy(&servicePoller);
    delete printer;
  }

  void ParallelSolverImpl::giveUp() {
    klee_error("ParallelSolverImpl: Giving up!");
  }
  
  void ParallelSolverImpl::setCoreSolverTimeout(double _timeout) {
    timeout = _timeout;
  }
  
  char* ParallelSolverImpl::getConstraintLog(const Query& q) {
    std::string constraintLog;
    buildSMTLIBv2String(q, constraintLog);

    // XXX the return value of this function shouldn't be char*
    char* ret = new char[ constraintLog.length() + 1 ];
    strcpy(ret, constraintLog.c_str());

    return ret;
  }
  
  bool ParallelSolverImpl::computeTruth(const Query& query, bool& isValid) {
    
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
  
  bool ParallelSolverImpl::computeValue(const Query& query, ref<Expr>& result) {
    
    bool success = false;
    std::vector<const Array*> objects;
    std::vector<std::vector<unsigned char> > values;
    bool hasSolution;
    
    // Find the object used in the expression, and compute an assignment for them.
    findSymbolicObjects(query.expr, objects);
    if (computeInitialValues(query.withFalse(), objects, values, hasSolution)) {
      assert(hasSolution && "state has invalid constraint set");
      // Evaluate the expression with the computed assignment.
      Assignment a(objects, values);
      result = a.evaluate(query.expr);
      success = true;
    }
    
    return (success);
  }
  
  bool ParallelSolverImpl::computeInitialValues(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values, bool& hasSolution) {
    
    _runStatusCode = SOLVER_RUN_STATUS_FAILURE;
    
    TimerStatIncrementer t(stats::queryTime);
    
    ++stats::queries;
    ++stats::queryCounterexamples;
    
    _runStatusCode = solveRemotely(query, objects, values, hasSolution);
    bool success = ((SOLVER_RUN_STATUS_SUCCESS_SOLVABLE == _runStatusCode)
        || (SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE == _runStatusCode));
    
    if (success) {
      if (hasSolution) {
        ++stats::queriesInvalid;
      } else {
        ++stats::queriesValid;
      }
    }
    
    return success;
  }

  SolverImpl::SolverRunStatus ParallelSolverImpl::solveRemotely(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values,
      bool& hasSolution) {

    std::string smtLibQuery;
    buildSMTLIBv2String(query, objects, smtLibQuery);

    SolverReply queryResult = sendQuery(smtLibQuery);

    int status = queryResult.status; 
    SolverImpl::SolverRunStatus ret;
    if(status == 0){
      assert(queryResult.reply);
      ret = parseSolverOutput(queryResult.reply, objects, values, hasSolution);
    } else if (status == 1){
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
    } else if (status == 2){
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_TIMEOUT;
    } else {
      ret = SolverImpl::SolverRunStatus::SOLVER_RUN_STATUS_FAILURE;
    }
    /*
     * would be nice to have this automatically in the destructor of SolverReply,
     * but Boost Fiber (in future.get() via Boost Optional) makes a copy of the object,
     * thus the memory would be freed earlier than we need
     */  
    zstr_free(&queryResult.reply);
    return ret;
  }

  int ParallelSolverImpl::generateRequestId(){
    if(++reqId > maxId){
      reqId = 0;
    }
    return reqId;
  }

  ParallelSolverImpl::SolverReply ParallelSolverImpl::sendQuery(std::string query){
    // std::cout << id << " starts\n";
    // std::cout << "Sending SMT query to sock\n";
    int req_id = generateRequestId();
    zstr_sendm(serviceActor, std::to_string(req_id).c_str());
    int rc = zstr_send(serviceActor, query.c_str());
    assert(rc == 0);
//    std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " sent query\n";
    
    bool gotOwnResponse = false;
    SolverReply solver_reply;
    while (zsock_events(serviceActor) & ZMQ_POLLIN) {
      zmsg_t* msg = zmsg_recv(serviceActor);
      char* response_id = zmsg_popstr(msg);
      char* response_status = zmsg_popstr(msg);

      int resp_id = std::stoi(response_id);
      int resp_status = std::stoi(response_status);

      char* response = nullptr;
      if(resp_status == 0){
        response = zmsg_popstr(msg);
      }
      solver_reply = SolverReply(resp_status, response);

      zstr_free(&response_id);
      zstr_free(&response_status);
      zmsg_destroy(&msg);
      //          std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " received reply\n";
      
      if(req_id == resp_id){
        gotOwnResponse = true;
        std::cout << "Got own response immediately\n";
      } else {
        auto elem = pendingQueries.find(resp_id);
        
        if (elem == pendingQueries.end()){
          std::cout << "Promise not found\n";
        } else {
          elem->second.set_value(solver_reply);
        }
      }
    }

    if(!gotOwnResponse){
      boost::fibers::promise<SolverReply> p;
      boost::fibers::future<SolverReply> f = p.get_future();
      pendingQueries.insert(std::make_pair(req_id, std::move(p)));
  
      solver_reply = f.get();
      pendingQueries.erase(req_id);
    }
    
    if (solver_reply.isEmpty()){
      std::cerr << "Received \"null\" response from server\n";
    }
    return solver_reply;
  }

  void ParallelSolverImpl::waitForResponse(){
    while (!(zsock_events(serviceActor) & ZMQ_POLLIN)){
      void* ret = zpoller_wait(servicePoller, 500);
      if(ret == NULL){
        if(zpoller_terminated(servicePoller)){
          std::cout << "Service poller terminated\n";
        } else {
          std::cout << "Service poller failed (unknown reason)\n";
        }
        return;
      }
    }
    while (zsock_events(serviceActor) & ZMQ_POLLIN) {
      zmsg_t* msg = zmsg_recv(serviceActor);
      char* response_id = zmsg_popstr(msg);
      char* response_status = zmsg_popstr(msg);

      int resp_id = std::stoi(response_id);
      int resp_status = std::stoi(response_status);

      char* response = nullptr;
      if(resp_status == 0){
        response = zmsg_popstr(msg);
      }
      SolverReply solver_reply(resp_status, response);

      zstr_free(&response_id);
      zstr_free(&response_status);
      zmsg_destroy(&msg);
      
      auto elem = pendingQueries.find(resp_id);
      
      if (elem == pendingQueries.end()){
        std::cout << "Promise not found\n";
      } else {
        elem->second.set_value(solver_reply);
      }
    }
  }
  
  SolverImpl::SolverRunStatus ParallelSolverImpl::parseSolverOutput(char* solverOutput,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values,
      bool& hasSolution){

    // XXX string is copied here, create non-copying std::streambuf
    std::istringstream iss(solverOutput);

    lexer.setInput(iss);

    SMTLIBOutputLexer::Token t = SMTLIBOutputLexer::UNRECOGNISED_TOKEN;

    /* The first thing we want to check is if the solver thought the
     * set of assertions was satisfiable
     */
    if (!lexer.getNextToken(t)) {
      klee_warning("ParallelSolverImpl: Lexer failed to get token");
      return SOLVER_RUN_STATUS_FAILURE;
    }

    switch (t) {
      case SMTLIBOutputLexer::UNKNOWN_TOKEN:
        klee_warning("ParallelSolverImpl : Solver responded unknown");
        return SOLVER_RUN_STATUS_FAILURE;
      case SMTLIBOutputLexer::UNSAT_TOKEN:
        //not satisfiable
        hasSolution = false;
        return SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
      case SMTLIBOutputLexer::SAT_TOKEN:
        hasSolution = true;
        break;
      default:
        std::cerr << "ParallelSolverImpl : Unexpected token `"
        << lexer.getLastTokenContents() << "`" << std::endl;
        giveUp();
        return SOLVER_RUN_STATUS_FAILURE;
    }

    //If we reach here the solver thought the assertions where satisfiable.
    if (objects.empty()) {
      //we weren't ask to get any values
      return SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }

    //Preemptively make space seeing as we known how many arrays there are.
    values.reserve(objects.size());

    /* We expected output like
     * (((select unnamed_1 (_ bv0 32) ) #x20))
     */

    unsigned int arrayNumber = 0;
    unsigned char byteValue = 0;
    //Loop over the arrays to retrieve their values.
    for (std::vector<const Array*>::const_iterator it = objects.begin();
        it != objects.end(); it++, arrayNumber++) {
      //The raw bits for this array will go in here
      std::vector<unsigned char> data;
      data.reserve((*it)->size);
      
      //Loop over the bytes in the array
      for (unsigned int byteNumber = 0; byteNumber < (*it)->size;
          byteNumber++) {

        // Expect "((("
        for (int c = 0; c < 3; c++) {
          if (!lexer.getNextToken(t)
              || t != SMTLIBOutputLexer::LBRACKET_TOKEN) {
            klee_error(
                "ParallelSolverImpl: Lexer failed to get token for array assignment. Expected `(`");
            return SOLVER_RUN_STATUS_FAILURE;
          }
        }
        
        // Expect "select"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::SELECT_TOKEN) {
          klee_error(
              "ParallelSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        // Expect the array name
        if (!lexer.getNextToken(t)
            || t != SMTLIBOutputLexer::ARRAY_IDENTIFIER_TOKEN
            || (*it)->name != lexer.getLastTokenContents()) {
          std::cerr
          << "ParallelSolverImpl: Lexer failed to get array identifier token."
          << std::endl << "Expected array name `" << (*it)->name
          << "`. Instead received token `" << lexer.getLastTokenContents()
          << "`" << std::endl;
          giveUp();
          return SOLVER_RUN_STATUS_FAILURE;
        }

        // Expect the array index
        unsigned long foundByteNumber = 0;
        if (!lexer.getNextToken(t)
            || t != SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN
            || !lexer.getLastNumericValue(foundByteNumber)
            || foundByteNumber != byteNumber) {
          klee_warning(
              "ParallelSolverImpl : Lexer failed to get token for array assignment.");
          std::cerr << "Expected (_ bv" << foundByteNumber << " "
              << (*it)->getDomain() << " ). Instead received"
              "token " << lexer.getLastTokenContents() << std::endl;
          giveUp();
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect ")"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::RBRACKET_TOKEN) {
          klee_error(
              "ParallelSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect the array value, we support multiple formats
        unsigned long determinedByteValue = 0;
        if (!lexer.getNextToken(t)
            || (t != SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE16_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE2_TOKEN)) {
          klee_error(
              "ParallelSolverImpl : Lexer failed to get token for array assignment."
              " Expected bitvector value.");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (!lexer.getLastNumericValue(determinedByteValue)) {
          klee_error(
              "ParallelSolverImpl : Lexer could not get the numeric value of the "
              "found bitvector constant");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (determinedByteValue > 255) {
          klee_error(
              "ParallelSolverImpl: Determined value for bitvector byte was out of range!");
        }

        byteValue = determinedByteValue;

        /* Perform the assignment. We assume for now the the "byteNumber"
         * corresponds with what KLEE expects.
         */
        data.push_back(byteValue);

        // Expect "))"
        for (int c = 0; c < 2; c++) {
          if (!lexer.getNextToken(t)
              || t != SMTLIBOutputLexer::RBRACKET_TOKEN) {
            klee_error(
                "ParallelSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
            return SOLVER_RUN_STATUS_FAILURE;
          }
        }

      }
      
      values.push_back(data);
      
    }

    //We found satisfiability and determined the array values successfully.
    return SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }

  std::string& ParallelSolverImpl::buildSMTLIBv2String(const Query& q,
      const std::vector<const Array*>& arrays, std::string& smtLibString){
    llvm::raw_string_ostream os(smtLibString);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->setArrayValuesToGet(arrays);
    printer->generateOutput();

    return os.str();
  }

  std::string& ParallelSolverImpl::buildSMTLIBv2String(const Query& q, std::string& smtLibString){
    llvm::raw_string_ostream os(smtLibString);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->generateOutput();

    return os.str();
  }

  SolverImpl::SolverRunStatus ParallelSolverImpl::getOperationStatusCode() {
    return _runStatusCode;
  }

}
