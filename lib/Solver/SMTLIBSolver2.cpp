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
#include "klee/util/ExprSMTLIBPrinter.h"

//for findSymbolicObjects()
#include "klee/util/ExprUtil.h"

#include "klee/util/Assignment.h"
#include "../Core/Common.h"

//remove me
#include <iostream>

#include <fstream>

#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <errno.h>
#include <sys/wait.h>
#include <sys/stat.h>

#include "SMTLIBOutputLexer.h"

#include "SolverStats.h"

#include "llvm/Support/CommandLine.h"
namespace SMTLIBSolverOpts {
  llvm::cl::opt<bool> makeHumanReadableSMTLIB("smtlibv2-solver-human-readable",
      llvm::cl::desc(
          "If using smtlibv2 solver make the queries human readable (default=off) (see -solver)."),
      llvm::cl::init(false));
}

using namespace std;
namespace klee {
  class SMTLIBSolverImpl: public SolverImpl {
    protected:
      string solverAddress;
      SMTLIBOutputLexer lexer;

      timespec timeout;
      timespec startTime;

      SolverRunStatus _runStatusCode;

      ExprSMTLIBPrinter* printer;

      void giveUp();
      bool haveRunOutOfTime();

      bool generateSMTLIBv2File(const Query& q,
          const std::vector<const Array*> arrays);
      virtual bool invokeSolver(const Query& q,
          const std::vector<const Array*> arrays);
      bool parseSolverOutput(const std::vector<const Array*> &objects,
          std::vector<std::vector<unsigned char> > &values, bool &hasSolution);

    public:
      SMTLIBSolverImpl(const string& _solverAddress);
      ~SMTLIBSolverImpl();

      ///Set the time in seconds to wait for the solver to complete.
      ///This time is rounded to the nearest second.
      ///The default is 0 (i.e. no timeout)
      void setCoreSolverTimeout(double _timeout);

      char* getConstraintLog(const Query&);

      bool computeTruth(const Query&, bool &isValid);
      bool computeValue(const Query&, ref<Expr> &result);
      bool computeInitialValues(const Query&,
          const std::vector<const Array*> &objects,
          std::vector<std::vector<unsigned char> > &values, bool &hasSolution);

      SolverRunStatus getOperationStatusCode();
  };
  
  SMTLIBSolver::SMTLIBSolver(std::string& solverAddress) :
      Solver(new SMTLIBSolverImpl(solverAddress)) {
  }
  
  void SMTLIBSolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  char *SMTLIBSolver::getConstraintLog(const Query& query) {
    return (impl->getConstraintLog(query));
  }
  
  void SMTLIBSolver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
  }
  
  // ------------------------------------- SMTLIBSolverImpl methods ----------------------------------------
  
  SMTLIBSolverImpl::SMTLIBSolverImpl(const string& _solverAddress) :
      solverAddress(_solverAddress), printer(NULL), _runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
    // FIXME there should be an initial run status code (e.g. _UNKNOWN or _RUNNING)
    /* Let the command line set which printer to use. */
    printer = new ExprSMTLIBPrinter();
    //set options
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(SMTLIBSolverOpts::makeHumanReadableSMTLIB);
    
    timeout.tv_nsec = timeout.tv_sec = 0;
    
    cerr << "KLEE: Using external SMTLIBv2 solver service:" << solverAddress
        << endl;
  }
  
  SMTLIBSolverImpl::~SMTLIBSolverImpl() {
    delete printer;
  }
  
  void SMTLIBSolverImpl::giveUp() {
    klee_error("SMTLIBSolverImpl: Giving up!");
  }
  
  void SMTLIBSolverImpl::setCoreSolverTimeout(double _timeout) {
    if (_timeout < 0.0) {
      timeout.tv_nsec = 0;
      timeout.tv_sec = 0;
    } else {
      timeout.tv_nsec = 0;
      //the +0.5 is to simulate rounding
      timeout.tv_sec = static_cast<unsigned int>(_timeout + 0.5);
    }
  }
  
  char* SMTLIBSolverImpl::getConstraintLog(const Query& q) {
    std::string constraintLog;
    llvm::raw_string_ostream os(constraintLog);

    printer->setOutput(os);
    printer->setQuery(q);
    printer->generateOutput();

    // return const_cast<char*>(os.str().c_str()) would be more efficient
    // but this is safer
    char* ret;
    strcpy(ret, os.str().c_str());

    return ret;
  }
  
  bool SMTLIBSolverImpl::computeTruth(const Query& query, bool &isValid) {
    
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
  
  bool SMTLIBSolverImpl::computeValue(const Query& query, ref<Expr> &result) {
    
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
  
  bool SMTLIBSolverImpl::computeInitialValues(const Query &query,
      const std::vector<const Array*> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
    
    _runStatusCode = SOLVER_RUN_STATUS_FAILURE;
    
    TimerStatIncrementer t(stats::queryTime);
    assert(_builder);
    
    /*
     * FIXME push() and pop() work for Z3 but not for Boolector.
     * If using Z3, use push() and pop() and assert constraints.
     * If using Boolector, assume constrainsts instead of asserting them.
     */
    //push(_meta_solver);
    if (!_useForked) {
      for (ConstraintManager::const_iterator it = query.constraints.begin(),
          ie = query.constraints.end(); it != ie; ++it) {
        //assertion(_meta_solver, _builder->construct(*it));
        assumption(_meta_solver, _builder->construct(*it));
      }
    }
    
    ++stats::queries;
    ++stats::queryCounterexamples;
    
    bool success = true;
    if (_useForked) {
      _runStatusCode = runAndGetCexForked(query, objects, values, hasSolution,
          _timeout);
      success = ((SOLVER_RUN_STATUS_SUCCESS_SOLVABLE == _runStatusCode)
          || (SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE == _runStatusCode));
    } else {
      _runStatusCode = runAndGetCex(query.expr, objects, values, hasSolution);
      success = true;
    }
    
    if (success) {
      if (hasSolution) {
        ++stats::queriesInvalid;
      } else {
        ++stats::queriesValid;
      }
    }
    
    //pop(_meta_solver);
    
    return (success);
  }
  
  SolverImpl::SolverRunStatus SMTLIBSolverImpl::runAndGetCex(
      ref<Expr> query_expr, const std::vector<const Array*> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
    
    // assume the negation of the query
    assumption(_meta_solver,
        _builder->construct(Expr::createIsZero(query_expr)));
    hasSolution = solve(_meta_solver);
    
    if (hasSolution) {
      values.reserve(objects.size());
      for (std::vector<const Array*>::const_iterator it = objects.begin(), ie =
          objects.end(); it != ie; ++it) {
        
        const Array *array = *it;
        assert(array);
        typename SolverContext::result_type array_exp =
            _builder->getInitialArray(array);
        
        std::vector<unsigned char> data;
        data.reserve(array->size);
        
        for (unsigned offset = 0; offset < array->size; offset++) {
          typename SolverContext::result_type elem_exp = evaluate(_meta_solver,
              SMTLIB::logic::Array::select(array_exp,
                  bvuint(offset, array->getDomain())));
          unsigned char elem_value = SMTLIB::read_value(_meta_solver, elem_exp);
          data.push_back(elem_value);
        }
        
        values.push_back(data);
      }
    }
    
    if (true == hasSolution) {
      return (SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE);
    } else {
      return (SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE);
    }
  }
  
  static void SMTLIBTimeoutHandler(int x) {
    _exit(52);
  }
  
  SolverImpl::SolverRunStatus SMTLIBSolverImpl::runAndGetCexForked(
      const Query &query, const std::vector<const Array*> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution,
      double timeout) {
    unsigned char *pos = shared_memory_ptr;
    unsigned sum = 0;
    for (std::vector<const Array*>::const_iterator it = objects.begin(), ie =
        objects.end(); it != ie; ++it) {
      sum += (*it)->size;
    }
    // sum += sizeof(uint64_t);
    sum += sizeof(stats::queryConstructs);
    assert(
        sum < shared_memory_size
            && "not enough shared memory for counterexample");
    
    fflush(stdout);
    fflush(stderr);
    int pid = fork();
    if (pid == -1) {
      fprintf(stderr, "error: fork failed (for SMTLIB)");
      return (SolverImpl::SOLVER_RUN_STATUS_FORK_FAILED);
    }
    
    if (pid == 0) {
      if (timeout) {
        ::alarm(0); /* Turn off alarm so we can safely set signal handler */
        ::signal(SIGALRM, SMTLIBTimeoutHandler);
        ::alarm(std::max(1, (int) timeout));
      }
      
      for (ConstraintManager::const_iterator it = query.constraints.begin(),
          ie = query.constraints.end(); it != ie; ++it) {
        assertion(_meta_solver, _builder->construct(*it));
        //assumption(_meta_solver, _builder->construct(*it));
      }
      
      std::vector<std::vector<typename SolverContext::result_type> > aux_arr_exprs;
      if (UseSMTLIB == SMTLIB_BACKEND_BOOLECTOR) {
        for (std::vector<const Array*>::const_iterator it = objects.begin(),
            ie = objects.end(); it != ie; ++it) {
          
          std::vector<typename SolverContext::result_type> aux_arr;
          const Array *array = *it;
          assert(array);
          typename SolverContext::result_type array_exp =
              _builder->getInitialArray(array);
          
          for (unsigned offset = 0; offset < array->size; offset++) {
            typename SolverContext::result_type elem_exp = evaluate(
                _meta_solver,
                SMTLIB::logic::Array::select(array_exp,
                    bvuint(offset, array->getDomain())));
            aux_arr.push_back(elem_exp);
          }
          aux_arr_exprs.push_back(aux_arr);
        }
        assert(aux_arr_exprs.size() == objects.size());
      }
      
      // assume the negation of the query
      // can be also asserted instead of assumed as we are in a child process
      assumption(_meta_solver,
          _builder->construct(Expr::createIsZero(query.expr)));
      unsigned res = solve(_meta_solver);
      
      if (res) {
        
        if (UseSMTLIB != SMTLIB_BACKEND_BOOLECTOR) {
          
          for (std::vector<const Array*>::const_iterator it = objects.begin(),
              ie = objects.end(); it != ie; ++it) {
            
            const Array *array = *it;
            assert(array);
            typename SolverContext::result_type array_exp =
                _builder->getInitialArray(array);
            
            for (unsigned offset = 0; offset < array->size; offset++) {
              
              typename SolverContext::result_type elem_exp = evaluate(
                  _meta_solver,
                  SMTLIB::logic::Array::select(array_exp,
                      bvuint(offset, array->getDomain())));
              unsigned char elem_value = SMTLIB::read_value(_meta_solver,
                  elem_exp);
              *pos++ = elem_value;
            }
          }
        } else {
          typename std::vector<std::vector<typename SolverContext::result_type> >::const_iterator
              eit = aux_arr_exprs.begin(), eie = aux_arr_exprs.end();
          for (std::vector<const Array*>::const_iterator it = objects.begin(),
              ie = objects.end(); it != ie, eit != eie; ++it, ++eit) {
            const Array *array = *it;
            const std::vector<typename SolverContext::result_type>& arr_exp =
                *eit;
            assert(array);
            assert(array->size == arr_exp.size());
            
            for (unsigned offset = 0; offset < array->size; offset++) {
              unsigned char elem_value = SMTLIB::read_value(_meta_solver,
                  arr_exp[offset]);
              *pos++ = elem_value;
            }
          }
        }
      }
      assert((uint64_t* ) pos);
      *((uint64_t*) pos) = stats::queryConstructs;
      
      _exit(!res);
    } else {
      int status;
      pid_t res;
      
      do {
        res = waitpid(pid, &status, 0);
      } while (res < 0 && errno == EINTR);
      
      if (res < 0) {
        fprintf(stderr, "error: waitpid() for SMTLIB failed");
        return (SolverImpl::SOLVER_RUN_STATUS_WAITPID_FAILED);
      }
      
      // From timed_run.py: It appears that linux at least will on
      // "occasion" return a status when the process was terminated by a
      // signal, so test signal first.
      if (WIFSIGNALED(status) || !WIFEXITED(status)) {
        fprintf(stderr,
            "error: SMTLIB did not return successfully (status = %d) \n",
            WTERMSIG(status));
        return (SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED);
      }
      
      int exitcode = WEXITSTATUS(status);
      if (exitcode == 0) {
        hasSolution = true;
      } else if (exitcode == 1) {
        hasSolution = false;
      } else if (exitcode == 52) {
        fprintf(stderr, "error: SMTLIB timed out");
        return (SolverImpl::SOLVER_RUN_STATUS_TIMEOUT);
      } else {
        fprintf(stderr, "error: SMTLIB did not return a recognized code");
        return (SolverImpl::SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE);
      }
      
      if (hasSolution) {
        values = std::vector<std::vector<unsigned char> >(objects.size());
        unsigned i = 0;
        for (std::vector<const Array*>::const_iterator it = objects.begin(),
            ie = objects.end(); it != ie; ++it) {
          const Array *array = *it;
          assert(array);
          std::vector<unsigned char> &data = values[i++];
          data.insert(data.begin(), pos, pos + array->size);
          pos += array->size;
        }
      }
      stats::queryConstructs += (*((uint64_t*) pos) - stats::queryConstructs);
      
      if (true == hasSolution) {
        return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
      } else {
        return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
      }
    }
  }
  
  SolverImpl::SolverRunStatus SMTLIBSolverImpl::getOperationStatusCode() {
    return _runStatusCode;
  }

}
