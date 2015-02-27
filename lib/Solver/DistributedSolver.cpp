//===-- SMTLIBSolver.cpp ------------------------------------------*- C++ -*-===//
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
#include "zmq_asio_socket.hpp"

#include "llvm/Support/CommandLine.h"

#include <czmq.h>

#include <boost/bind.hpp>
#include <boost/asio/io_service.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/future.hpp>
#include <boost/fiber/asio/spawn.hpp>
#include <boost/fiber/asio/loop.hpp>
#include <unordered_map>

namespace SMTLIBSolverOpts {
  llvm::cl::opt<bool> makeHumanReadableSMTLIB("smtlibv2-solver-human-readable",
      llvm::cl::desc(
          "If using smtlibv2 solver make the queries human readable (default=off) (see -solver)."),
          llvm::cl::init(false));
}

using namespace std;
namespace klee {
  class DistributedSolverImpl: public SolverImpl {
    private:
      SMTLIBOutputLexer lexer;

      double timeout;

      SolverRunStatus _runStatusCode;

      ExprSMTLIBPrinter* printer;

      boost::asio::io_service ioService;

      zsock_t* discovery;
      zsock_t* service;
      zmq_asio_socket* serviceAsio;
      zhashx_t* solvers;

      boost::fibers::fiber loopFiber;

      std::unordered_map<unsigned int, boost::fibers::promise<std::string>> pendingQueries;

      int reqId;
      const unsigned int maxId = UINT_MAX-1;

      bool stopped;

      void giveUp();

      void findAndSetSolverBackends();
      const boost::asio::io_service& getAsioIoService() const;
      std::string buildSMTLIBv2String(const Query& q,
          const std::vector<const Array*>& arrays);
      std::string buildSMTLIBv2String(const Query& q);
      int generateRequestId();
      std::string sendQuery(std::string query);
      void receiveSolverResponse(boost::fibers::asio::yield_context yield);
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
      virtual void stop();
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

  void DistributedSolver::stop() {
    (static_cast<DistributedSolverImpl*>(impl))->stop();
  }
  
  // ------------------------------------- SMTLIBSolverImpl methods ----------------------------------------
  
  DistributedSolverImpl::DistributedSolverImpl(const string _solverAddress) :
          timeout(0.0), _runStatusCode(SOLVER_RUN_STATUS_FAILURE), discovery(zsock_new_req(_solverAddress.c_str())),
          service(zsock_new(ZMQ_DEALER)), solvers(NULL), reqId(0), stopped(false) {
    // FIXME there should be an initial run status code (e.g. _UNKNOWN or _RUNNING)
    printer = new ExprSMTLIBPrinter();
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(SMTLIBSolverOpts::makeHumanReadableSMTLIB);
    assert(discovery);
    assert(service);

    serviceAsio = new zmq_asio_socket(service, ioService);
    // XXX is this needed?
    serviceAsio->non_blocking(true);

//    std::cout << "client1 starting...\n";
    findAndSetSolverBackends();

//    boost::fibers::asio::spawn(ioService, boost::bind(receiveSolverResponse, std::ref(serviceAsio), _1));
    boost::fibers::asio::spawn(ioService, [&] (boost::fibers::asio::yield_context yield) { receiveSolverResponse(yield); });
    loopFiber = boost::fibers::fiber(boost::bind(boost::fibers::asio::run_service, std::ref(ioService)));
  }

  DistributedSolverImpl::~DistributedSolverImpl() {
    zhashx_destroy(&solvers);
    zsock_set_linger(service, 0);
    delete serviceAsio;
    zsock_destroy(&discovery);
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

  const boost::asio::io_service& DistributedSolverImpl::getAsioIoService() const{
    return ioService;
  }

  void DistributedSolverImpl::giveUp() {
    klee_error("SMTLIBSolverImpl: Giving up!");
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

    std::string queryResult;
    queryResult = sendQuery(smtLibQuery);

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
    // boost::system::error_code ec;
    // if((zsock_events(service) & ZMQ_POLLOUT) != ZMQ_POLLOUT){
    //  boost::asio::async_write(asio_sock, boost::asio::null_buffers(), boost::fibers::asio::yield[ec]);
    // }
    // std::cout << "Sending SMT query to sock\n";
    int id = generateRequestId();
    zstr_sendm(service, std::to_string(id).c_str());
    int rc = zstr_send(service, query.c_str());
    assert(rc == 0);
//    std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " sent query\n";

    boost::fibers::promise<std::string> p;
    boost::fibers::future<std::string> f = p.get_future();
    pendingQueries.insert(std::make_pair(id, std::move(p)));

    std::string ans = f.get();

    if (ans.empty()){
      std::cerr << "Received \"null\" response from server\n";
    }

    pendingQueries.erase(id);
    return ans;
  }

  void DistributedSolverImpl::receiveSolverResponse(boost::fibers::asio::yield_context yield){
    boost::system::error_code ec;
    while(!stopped){
      if(!(zsock_events(service) & ZMQ_POLLIN)){
        serviceAsio->async_read_some(boost::asio::null_buffers(), yield[ec]);
        if(stopped){
//          std::cout << "Reader stopping\n";
          break;
        }
      }
      while(zsock_events(service) & ZMQ_POLLIN){
        zmsg_t* msg = zmsg_recv(service);
        char* response_id = zmsg_popstr(msg);
        char* response = zmsg_popstr(msg);
        zmsg_destroy(&msg);
        //          std::cout << boost::fibers::detail::scheduler::instance()->active()->get_id() << " received reply\n";

        auto elem = pendingQueries.find(std::stoi(response_id));

        if ( elem == pendingQueries.end() ){
          std::cout << "Promise not found\n";
        }
        else {
          elem->second.set_value(std::string(response));
        }

        zstr_free(&response_id);
        zstr_free(&response);
        //          boost::this_fiber::yield();
      }
//      boost::this_fiber::yield();
    }
  }

  void DistributedSolverImpl::stop(){
    stopped = true;
    serviceAsio->cancel();
    // Give the reader a chance to exit. If we stop the io_service, it will be stuck.
    boost::this_fiber::yield();
    ioService.stop();
//    std::cout << "Joining loop fiber\n";
    loopFiber.join();
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
      klee_warning("SMTLIBSolverImpl: Lexer failed to get token");
      return SOLVER_RUN_STATUS_FAILURE;
    }

    switch (t) {
      case SMTLIBOutputLexer::UNKNOWN_TOKEN:
        klee_warning("SMTLIBSolverImpl : Solver responded unknown");
        return SOLVER_RUN_STATUS_FAILURE;
      case SMTLIBOutputLexer::UNSAT_TOKEN:
        //not satisfiable
        hasSolution = false;
        return SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
      case SMTLIBOutputLexer::SAT_TOKEN:
        hasSolution = true;
        break;
      default:
        cerr << "SMTLIBSolverImpl : Unexpected token `"
        << lexer.getLastTokenContents() << "`" << endl;
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
                "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `(`");
            return SOLVER_RUN_STATUS_FAILURE;
          }
        }
        
        // Expect "select"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::SELECT_TOKEN) {
          klee_error(
              "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        // Expect the array name
        if (!lexer.getNextToken(t)
            || t != SMTLIBOutputLexer::ARRAY_IDENTIFIER_TOKEN
            || (*it)->name != lexer.getLastTokenContents()) {
          cerr
          << "SMTLIBSolverImpl: Lexer failed to get array identifier token."
          << endl << "Expected array name `" << (*it)->name
          << "`. Instead received token `" << lexer.getLastTokenContents()
          << "`" << endl;
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
              "SMTLIBSolverImpl : Lexer failed to get token for array assignment.");
          cerr << "Expected (_ bv" << foundByteNumber << " "
              << (*it)->getDomain() << " ). Instead received"
              "token " << lexer.getLastTokenContents() << endl;
          giveUp();
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect ")"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::RBRACKET_TOKEN) {
          klee_error(
              "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        //Expect the array value, we support multiple formats
        unsigned long determinedByteValue = 0;
        if (!lexer.getNextToken(t)
            || (t != SMTLIBOutputLexer::NUMERAL_BASE10_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE16_TOKEN
                && t != SMTLIBOutputLexer::NUMERAL_BASE2_TOKEN)) {
          klee_error(
              "SMTLIBSolverImpl : Lexer failed to get token for array assignment."
              " Expected bitvector value.");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (!lexer.getLastNumericValue(determinedByteValue)) {
          klee_error(
              "SMTLIBSolverImpl : Lexer could not get the numeric value of the "
              "found bitvector constant");
          return SOLVER_RUN_STATUS_FAILURE;
        }

        if (determinedByteValue > 255) {
          klee_error(
              "SMTLIBSolverImpl: Determined value for bitvector byte was out of range!");
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
                "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
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
