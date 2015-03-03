//===-- DistributedSolver.cpp ------------------------------------------*- C++ -*-===//
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

#include "SMTLIBOutputLexer.h"

#include "SolverStats.h"

#include "llvm/Support/CommandLine.h"

#include <czmq.h>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/future.hpp>
#include <unordered_map>

namespace SMTLIBSolverOpts {
  llvm::cl::opt<bool> makeHumanReadableSMTLIB("smtlibv2-solver-human-readable",
      llvm::cl::desc(
          "If using smtlibv2 solver make the queries human readable (default=off) (see -solver)."),
          llvm::cl::init(false));
}

namespace klee {
  class DistributedSolverImpl: public SolverImpl {
    private:
      SMTLIBOutputLexer lexer;

      double timeout;

      SolverRunStatus _runStatusCode;

      ExprSMTLIBPrinter* printer;

      zsock_t* discovery;
      zsock_t* service;
      zpoller_t* service_poller;
      zhashx_t* solvers;

      std::unordered_map<unsigned int, boost::fibers::promise<std::string>> pendingQueries;

      unsigned int reqId;
      const unsigned int maxId = UINT_MAX-1;


      void giveUp();

      void findAndSetSolverBackends();
      std::string buildSMTLIBv2String(const Query& q,
          const std::vector<const Array*>& arrays);
      std::string buildSMTLIBv2String(const Query& q);
      int generateRequestId();
      std::string sendQuery(std::string query);
      virtual SolverImpl::SolverRunStatus solveRemotely(const Query& q,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values,
          bool& hasSolution);
      SolverImpl::SolverRunStatus parseSolverOutput(const std::string& solverOutput,
          const std::vector<const Array*>& objects,
          std::vector<std::vector<unsigned char> >& values,
          bool& hasSolution);

    public:
      DistributedSolverImpl(const std::string _solverAddress);
      ~DistributedSolverImpl();

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
  
  DistributedSolver::DistributedSolver(std::string solverAddress) :
          Solver(new DistributedSolverImpl(solverAddress)) {
  }
  
  DistributedSolver::~DistributedSolver(){
  }

  void DistributedSolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  char* DistributedSolver::getConstraintLog(const Query& query) {
    return (impl->getConstraintLog(query));
  }

  void DistributedSolver::waitForResponse() {
    static_cast<DistributedSolverImpl*>(impl)->waitForResponse();
  }
  
  // ------------------------------------- DistributedSolverImpl methods ----------------------------------------
  
  DistributedSolverImpl::DistributedSolverImpl(const std::string _solverAddress) :
          timeout(0.0), _runStatusCode(SOLVER_RUN_STATUS_FAILURE), discovery(zsock_new_req(_solverAddress.c_str())),
          service(zsock_new(ZMQ_DEALER)), service_poller(zpoller_new(service, NULL)), solvers(NULL), reqId(0) {
    // FIXME there should be an initial run status code (e.g. _UNKNOWN or _RUNNING)
    printer = new ExprSMTLIBPrinter();
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(SMTLIBSolverOpts::makeHumanReadableSMTLIB);
    assert(discovery);
    assert(service);
    assert(service_poller);

    findAndSetSolverBackends();
  }

  DistributedSolverImpl::~DistributedSolverImpl() {
    zhashx_destroy(&solvers);
    zsock_set_linger(service, 0);
    zsock_destroy(&discovery);
    zpoller_destroy(&service_poller);
    zsock_destroy(&service);
    delete printer;
  }

  void DistributedSolverImpl::findAndSetSolverBackends(){
    int rc = zstr_send(discovery, "DISC");
    assert(rc == 0);
//    std::cout << "Sent discovery request\n";
    zframe_t* rep = zframe_recv(discovery);
    solvers = zhashx_unpack(rep);
    zframe_destroy(&rep);
//    std::cout << "Service endpoint(s) discovered: {\n";
    for(void* solver = zhashx_first(solvers); solver != NULL; solver = zhashx_next(solvers)){
      std::string solver_addr = (const char*)zhashx_cursor(solvers);
      zsock_connect(service, "%s%s", "tcp://", solver_addr.c_str());
//      std::cout << '\t' << solver_addr << "\n";
    }
//    std::cout << "}\n";
  }

  void DistributedSolverImpl::giveUp() {
    klee_error("DistributedSolverImpl: Giving up!");
  }
  
  void DistributedSolverImpl::setCoreSolverTimeout(double _timeout) {
    timeout = _timeout;
  }
  
  char* DistributedSolverImpl::getConstraintLog(const Query& q) {
    std::string constraintLog = buildSMTLIBv2String(q);

    // XXX the return value of this function shouldn't be char*
    char* ret = new char[ constraintLog.length() + 1 ];
    strcpy(ret, constraintLog.c_str());

    return ret;
  }
  
  bool DistributedSolverImpl::computeTruth(const Query& query, bool& isValid) {
    
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
  
  bool DistributedSolverImpl::computeValue(const Query& query, ref<Expr>& result) {
    
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
  
  bool DistributedSolverImpl::computeInitialValues(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values, bool& hasSolution) {
    
    _runStatusCode = SOLVER_RUN_STATUS_FAILURE;
    
    TimerStatIncrementer t(stats::queryTime);
    
    ++stats::queries;
    if (!objects.empty())
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

  SolverImpl::SolverRunStatus DistributedSolverImpl::solveRemotely(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values,
      bool& hasSolution) {

    std::string smtLibQuery = buildSMTLIBv2String(query, objects);

    std::string queryResult = sendQuery(smtLibQuery);

    return parseSolverOutput(queryResult, objects, values, hasSolution);
  }

  int DistributedSolverImpl::generateRequestId(){
    if(++reqId > maxId){
      reqId = 0;
    }
    return reqId;
  }

  std::string DistributedSolverImpl::sendQuery(std::string query){
    // std::cout << id << " starts\n";
    // std::cout << "Sending SMT query to sock\n";
    int req_id = generateRequestId();
    zstr_sendm(service, std::to_string(req_id).c_str());
    int rc = zstr_send(service, query.c_str());
    assert(rc == 0);
//    std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " sent query\n";
    
    std::string solution;
    bool gotOwnResponse = false;
    while (zsock_events(service) & ZMQ_POLLIN) {
      zmsg_t* msg = zmsg_recv(service);
      char* response_id = zmsg_popstr(msg);
      char* response = zmsg_popstr(msg);
      zmsg_destroy(&msg);
      //          std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " received reply\n";
      
      int resp_id = std::stoi(response_id);

      if(req_id == resp_id){
        gotOwnResponse = true;
        solution = response;
      } else {
        auto elem = pendingQueries.find(resp_id);
        
        if (elem == pendingQueries.end()){
          std::cout << "Promise not found\n";
        } else {
          elem->second.set_value(std::string(response));
        }
      }

      zstr_free(&response_id);
      zstr_free(&response);
    }

    if(!gotOwnResponse){
      boost::fibers::promise<std::string> p;
      boost::fibers::future<std::string> f = p.get_future();
      pendingQueries.insert(std::make_pair(req_id, std::move(p)));
  
      solution = f.get();
      pendingQueries.erase(req_id);
    }
    
    if (solution.empty()){
      std::cerr << "Received \"null\" response from server\n";
    }
    return solution;
  }

  void DistributedSolverImpl::waitForResponse(){
    while (!(zsock_events(service) & ZMQ_POLLIN)){
      void* ret = zpoller_wait(service_poller, -1);
      if(ret == NULL){
        if(zpoller_terminated(service_poller)){
          std::cout << "Service poller terminated\n";
        } else if (zpoller_expired(service_poller)){
          std::cout << "Service poller expired\n";
        } else {
          std::cout << "Service poller failed (unknown reason)\n";
        }
        return;
      }
    }
    while (zsock_events(service) & ZMQ_POLLIN) {
      zmsg_t* msg = zmsg_recv(service);
      char* response_id = zmsg_popstr(msg);
      char* response = zmsg_popstr(msg);
      zmsg_destroy(&msg);
      
      auto elem = pendingQueries.find(std::stoi(response_id));
      
      if (elem == pendingQueries.end()){
        std::cout << "Promise not found\n";
      } else {
        elem->second.set_value(std::string(response));
      }
      
      zstr_free(&response_id);
      zstr_free(&response);
    }
  }
  
  SolverImpl::SolverRunStatus DistributedSolverImpl::parseSolverOutput(const std::string& solverOutput,
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
      klee_warning("DistributedSolverImpl: Lexer failed to get token");
      return SOLVER_RUN_STATUS_FAILURE;
    }

    switch (t) {
      case SMTLIBOutputLexer::UNKNOWN_TOKEN:
        klee_warning("DistributedSolverImpl : Solver responded unknown");
        return SOLVER_RUN_STATUS_FAILURE;
      case SMTLIBOutputLexer::UNSAT_TOKEN:
        //not satisfiable
        hasSolution = false;
        return SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
      case SMTLIBOutputLexer::SAT_TOKEN:
        hasSolution = true;
        break;
      default:
        std::cerr << "DistributedSolverImpl : Unexpected token `"
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
                "DistributedSolverImpl: Lexer failed to get token for array assignment. Expected `(`");
            return SOLVER_RUN_STATUS_FAILURE;
          }
        }
        
        // Expect "select"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::SELECT_TOKEN) {
          klee_error(
              "DistributedSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        // Expect the array name
        if (!lexer.getNextToken(t)
            || t != SMTLIBOutputLexer::ARRAY_IDENTIFIER_TOKEN
            || (*it)->name != lexer.getLastTokenContents()) {
          std::cerr
          << "DistributedSolverImpl: Lexer failed to get array identifier token."
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
              "DistributedSolverImpl : Lexer failed to get token for array assignment.");
          std::cerr << "Expected (_ bv" << foundByteNumber << " "
              << (*it)->getDomain() << " ). Instead received"
              "token " << lexer.getLastTokenContents() << std::endl;
          giveUp();
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect ")"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::RBRACKET_TOKEN) {
          klee_error(
              "DistributedSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect the array value, we support multiple formats
        unsigned long determinedByteValue = 0;
        if (!lexer.getNextToken(t)
            || (t != SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE16_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE2_TOKEN)) {
          klee_error(
              "DistributedSolverImpl : Lexer failed to get token for array assignment."
              " Expected bitvector value.");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (!lexer.getLastNumericValue(determinedByteValue)) {
          klee_error(
              "DistributedSolverImpl : Lexer could not get the numeric value of the "
              "found bitvector constant");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (determinedByteValue > 255) {
          klee_error(
              "DistributedSolverImpl: Determined value for bitvector byte was out of range!");
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
                "DistributedSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
            return SOLVER_RUN_STATUS_FAILURE;
          }
        }

      }
      
      values.push_back(data);
      
    }

    //We found satisfiability and determined the array values successfully.
    return SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }

  std::string DistributedSolverImpl::buildSMTLIBv2String(const Query& q,
      const std::vector<const Array*>& arrays){
    std::string smtLibString;
    llvm::raw_string_ostream os(smtLibString);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->setArrayValuesToGet(arrays);
    printer->generateOutput();

    os.flush();
    return smtLibString;
  }

  std::string DistributedSolverImpl::buildSMTLIBv2String(const Query& q){
    std::string smtLibString;
    llvm::raw_string_ostream os(smtLibString);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->generateOutput();

    os.flush();
    return smtLibString;
  }

  SolverImpl::SolverRunStatus DistributedSolverImpl::getOperationStatusCode() {
    return _runStatusCode;
  }

}
