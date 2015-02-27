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

#include "llvm/Support/CommandLine.h"

#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

using namespace std;
namespace klee {
  class SMTLIBSolverImpl: public SolverImpl {
    private:
      SMTLIBOutputLexer lexer;

      double timeout;

      SolverRunStatus _runStatusCode;

      std::string solverPath;
      bool IgnoreSolverFailures;

      ExprSMTLIBPrinter* printer;

      void giveUp();

      std::string buildSMTLIBv2String(const Query& q,
          const std::vector<const Array*>& arrays);
      std::string buildSMTLIBv2String(const Query& q);
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
      SMTLIBSolverImpl(const std::string _solverAddress);
      ~SMTLIBSolverImpl();

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
  
  SMTLIBSolver::SMTLIBSolver(std::string solverAddress) :
          Solver(new SMTLIBSolverImpl(solverAddress)) {
  }
  
  SMTLIBSolver::~SMTLIBSolver(){
  }

  void SMTLIBSolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  char* SMTLIBSolver::getConstraintLog(const Query& query) {
    return (impl->getConstraintLog(query));
  }
  
  // ------------------------------------- SMTLIBSolverImpl methods ----------------------------------------
  
  SMTLIBSolverImpl::SMTLIBSolverImpl(const string _solverAddress) :
          timeout(0.0), _runStatusCode(SOLVER_RUN_STATUS_FAILURE), solverPath(_solverAddress), IgnoreSolverFailures(false) {
    // FIXME there should be an initial run status code (e.g. _UNKNOWN or _RUNNING)
    printer = new ExprSMTLIBPrinter();
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(false);
  }

  SMTLIBSolverImpl::~SMTLIBSolverImpl() {
    delete printer;
  }

  void SMTLIBSolverImpl::giveUp() {
    klee_error("SMTLIBSolverImpl: Giving up!");
  }
  
  void SMTLIBSolverImpl::setCoreSolverTimeout(double _timeout) {
    timeout = _timeout;
  }
  
  char* SMTLIBSolverImpl::getConstraintLog(const Query& q) {
    std::string constraintLog = buildSMTLIBv2String(q);

    // XXX the return value of this function shouldn't be char*
    char* ret = new char[ constraintLog.length() + 1 ];
    strcpy(ret, constraintLog.c_str());

    return ret;
  }
  
  bool SMTLIBSolverImpl::computeTruth(const Query& query, bool& isValid) {
    
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
  
  bool SMTLIBSolverImpl::computeValue(const Query& query, ref<Expr>& result) {
    
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
  
  bool SMTLIBSolverImpl::computeInitialValues(const Query& query,
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

  SolverImpl::SolverRunStatus SMTLIBSolverImpl::solveRemotely(const Query& query,
      const std::vector<const Array*>& objects,
      std::vector<std::vector<unsigned char> >& values,
      bool& hasSolution) {

    std::string smtLibQuery = buildSMTLIBv2String(query, objects);

    std::string queryResult;
    queryResult = sendQuery(smtLibQuery);

    return parseSolverOutput(queryResult, objects, values, hasSolution);
  }

  std::string SMTLIBSolverImpl::sendQuery(std::string query){
    fflush(stdout);
    fflush(stderr);

    int p2cPipe[2];
    int c2pPipe[2];

    if(
        pipe(p2cPipe) ||
        pipe(c2pPipe)){
      std::cerr << "Failed to pipe\n";
      return "";
    }

    pid_t pid = fork();
    if (pid > 0) {
      // parent
      close(p2cPipe[0]);
      close(c2pPipe[1]);

      write(p2cPipe[1], query.c_str(), query.length()+1);
      close(p2cPipe[1]);

      int status;
      pid_t res;

      do {
        res = waitpid(pid, &status, 0);
      } while (res < 0 && errno == EINTR);

      if (res < 0) {
        fprintf(stderr, "ERROR: waitpid() for STP failed");
        if (!IgnoreSolverFailures)
          exit(1);
//        return SolverImpl::SOLVER_RUN_STATUS_WAITPID_FAILED;
        return "";
      }

      if (WIFSIGNALED(status) || !WIFEXITED(status)) {
        fprintf(stderr, "ERROR: STP did not return successfully.  Most likely you forgot to run 'ulimit -s unlimited'\n");
        if (!IgnoreSolverFailures)  {
          exit(1);
        }
//        return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
        return "";
      }

      bool hasSolution;
      int exitcode = WEXITSTATUS(status);
      if (exitcode==0) {
        hasSolution = true;
      } else if (exitcode==1) {
        hasSolution = false;
      } else if (exitcode==52) {
        fprintf(stderr, "error: STP timed out");
        // mark that a timeout occurred
//        return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
        return "";
      } else {
        fprintf(stderr, "error: STP did not return a recognized code");
        if (!IgnoreSolverFailures)
          exit(1);
//        return SolverImpl::SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE;
        return "";
      }

      if (hasSolution) {
        std::string ans;
        int readBytes = 1;
        char buf[100];

        while((readBytes = read(c2pPipe[0], buf, sizeof(buf)-1)) > 0){
          ans.append(buf, readBytes);
        }
        return ans;
      } else {
//        return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
        return "";
      }
    }
    else if (pid == 0) {
      // child
      if(
          dup2(p2cPipe[0], STDIN_FILENO) == -1 ||
          dup2(c2pPipe[1], STDOUT_FILENO) == -1 ||
          dup2(c2pPipe[1], STDERR_FILENO) == -1){
        std::cerr << "Failed to redirect stdin/stdout/stderr\n";
        exit(1);
      }
      close(p2cPipe[0]);
      close(p2cPipe[1]);
      close(c2pPipe[0]);
      close(c2pPipe[1]);

      int ret = execl(solverPath.c_str(), solverPath.c_str(), (char*)NULL);
      exit(ret);
    }
    else {
      std::cerr << "Failed to fork!\n";
      return "";
    }
  }

  SolverImpl::SolverRunStatus SMTLIBSolverImpl::parseSolverOutput(const std::string& solverOutput,
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

  std::string SMTLIBSolverImpl::buildSMTLIBv2String(const Query& q,
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

  std::string SMTLIBSolverImpl::buildSMTLIBv2String(const Query& q){
    std::string smtLibString;
    llvm::raw_string_ostream os(smtLibString);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->generateOutput();

    os.flush();
    return smtLibString;
  }

  SolverImpl::SolverRunStatus SMTLIBSolverImpl::getOperationStatusCode() {
    return _runStatusCode;
  }

}
