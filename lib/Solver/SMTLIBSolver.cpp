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
    static_cast<SMTLIBSolverImpl*>(impl)->setCoreSolverTimeout(timeout);
  }

  /*
   *  Implementation of SMTLIBSolverImpl methods
   */

  SMTLIBSolverImpl::SMTLIBSolverImpl(const string& _solverAddress) :
      solverAddress(_solverAddress), printer(NULL) {
    /* Let the command line set which printer to
     * use.
     */
    printer = new ExprSMTLIBPrinter();
    //set options
    printer->setLogic(ExprSMTLIBPrinter::QF_AUFBV);
    printer->setHumanReadable(SMTLIBSolverOpts::makeHumanReadableSMTLIB);

    timeout.tv_nsec = timeout.tv_sec = 0;

    cerr << "KLEE: Using external SMTLIBv2 solver service:" << solverAddress << endl;
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

  bool SMTLIBSolverImpl::computeTruth(const Query& query, bool &isValid) {
    std::vector<const Array*> objects;
    std::vector<std::vector<unsigned char> > values;
    bool hasSolution;

    if (!computeInitialValues(query, objects, values, hasSolution))
      return false;

    isValid = !hasSolution;
    return true;
  }

  bool SMTLIBSolverImpl::computeValue(const Query& query, ref<Expr> &result) {
    std::vector<const Array*> objects;
    std::vector<std::vector<unsigned char> > values;
    bool hasSolution;

    // Find the objects used in the expression, and compute an assignment
    // for them.
    findSymbolicObjects(query.expr, objects);
    if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
      return false;
    assert(hasSolution && "state has invalid constraint set");

    // Evaluate the expression with the computed assignment.
    Assignment a(objects, values);
    result = a.evaluate(query.expr);

    return true;
  }

  bool SMTLIBSolverImpl::computeInitialValues(const Query& query,
      const std::vector<const Array*> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
    //update statistics
    ++stats::queries;
    //we only query for a "counter example" is objects is not empty!
    if (!objects.empty())
      ++stats::queryCounterexamples;

    if (!invokeSolver(query, objects))
      return false;

    if (!parseSolverOutput(objects, values, hasSolution))
      return false;

    /* Odd but this is how the reset of klee works
     * sat == INVALID
     * unsat == VALID
     */
    if (hasSolution)
      ++stats::queriesInvalid;
    else
      ++stats::queriesValid;

    return true;
  }

  void SMTLIBSolverImpl::runChildCode(const Query&q,
      const std::vector<const Array*> arrays) {
    //child code

    //If we get killed before calling execlp() we don't want KLEE's signal handlers to be called.
    signal(SIGINT, SIG_DFL);
    signal(SIGQUIT, SIG_DFL);
    signal(SIGTERM, SIG_DFL);

    signal(SIGALRM, SIG_DFL); //The child process doesn't need the time updates.

    /* Generate the SMTLIBv2 query. We do it in the child because this process may take a long
     * time and so should be included as part of the timeout.
     */
    if (!generateSMTLIBv2File(q, arrays)) {
      klee_error("SMTLIBSolverImpl (Child) : Failed to generated query!");
      exit (specialExitCode);
    }

    //open the output file (truncate it) for the child and have stdout go into it
    if (freopen(pathToSolverOutputFile.c_str(), "w", stdout) == NULL) {
      klee_error("SMTLIBSolverImpl (Child): Child failed to redirect stdout.");
      exit (specialExitCode);
    }

    /* Invoke the solver. We pass it as the 1st argument the name of SMTLIBv2 file we generated
     * earlier.
     */
    if (execlp(pathToSolver.c_str(), pathToSolver.c_str(),
        pathToSolverInputFile.c_str(), (char*) NULL) == -1) {
      //We failed to invoke the solver
      switch (errno) {
        case ENAMETOOLONG:
          klee_warning(
              "SMTLIBSolverImpl (child): The SMTLIBv2 solver path is too long!");
          exit (specialExitCode);
        case ENOENT:
          cerr << "SMTLIBSolverImpl (child): The executable " << pathToSolver
              << " does not exist!" << endl;
          exit(specialExitCode);
        default:
          cerr << "SMTLIBSolverImpl (child): Failed to invoke solver ("
              << pathToSolver << ")" << endl;
          exit(specialExitCode);
      }
    }

  }

  bool SMTLIBSolverImpl::invokeSolver(const Query& q,
      const std::vector<const Array*> arrays) {
    //Record the start time
    if (clock_gettime(CLOCK_MONOTONIC, &startTime) == -1) {
      cerr << "SMTLIBSolverImpl: Failed to record start time." << endl;
    }

    /* before we fork we need to flush stdout.
     * If we don't the parent and child have the unflushed stdout
     * which can get outputted twice because both the parent and child flush stdout
     * see http://stackoverflow.com/questions/3513242/working-of-fork-in-linux-gcc
     */
    fflush(stdout);
    fflush(stderr);

    //Perform fork
    pid_t childPid = fork();
    if (childPid == -1) {
      klee_error("SMTLIBSolverImpl: Failed to fork!");
      return false;
    }

    if (childPid > 0) {
      //parent code
      int status = 0;
      int result = 0;

      /* This is a disgusting waste of CPU time. We've effectively got a polling wait
       * because KLEE has an interval timer set (see ExecutorTimers.cpp) to emit SIGALRM
       * periodically which interrupts waitpid()
       *
       * A more elegant solution than using waitpid() is to use sigtimedwait() (in conjunction
       * with waitpid() so we reap the child) for the timedwait but this requires that we block
       * SIGALRM which disrupts KLEE keeping track of time. For now this will do.
       *
       * Sometimes (e.g. Feature/SolverTimeout test case) the SIGALRM interval timer isn't set (why?)
       * so this could cause a permanent hang if we didn't use WNOHANG. When no child is
       * available waitpid() returns 0.
       *
       */
      do {
        result = waitpid(childPid, &status, WNOHANG);
      } while (!haveRunOutOfTime()
          && ((result == -1 && errno == EINTR) || result == 0));

      if (haveRunOutOfTime()) {
        klee_warning("SMTLIBSolverImpl: The Solver timed out!");
        kill(childPid, SIGTERM);
        cerr << "KLEE: SMTLIBSolverImpl: Reaping child process (" << childPid
            << ")...";
        cerr.flush();

        do {
          //Loop because we may get interrupted by SIGALRM
          result = waitpid(childPid, NULL, 0);
        } while (result == -1 && errno == EINTR);
        cerr << "done" << endl;

        //Perform any additonal needed clean up.
        performCleanUp();

        return false;
      }

      //Now we will do a clean up of the child process.
      if (result < 0) {
        klee_warning("SMTLIBSolverImpl: Failed to clean up child process.");
        performCleanUp();
        return false;
      }

      //Check that the child terminated normally (i.e. not via a signal).
      if (WIFEXITED(status)) {
        /* We cannot assume the solver exit code (WEXITSTATUS(status)) will be 0
         * because we may ask (check-sat) and go on to ask for array values as well (via (get-value () ).
         * If the solver returns "unsat" then it is incorrect to ask for array values which will result
         * in an error. The solver may give a bad exit code in this case but hopefully we still have parsable
         * output.
         */

        //check for our specialExitCode that indicates the child process failed in some way.
        if (WEXITSTATUS(status) == specialExitCode) {
          klee_warning("SMTLIBSolverImpl: The solver could not be executed.");
          performCleanUp();
          return false;
        }

        //We interpret any exit code (except the specialExitCode) of as a successful run of the solver
        return true;

      } else {
        klee_warning("SMTLIBSolverImpl: The Solver didn't exit normally.");
        performCleanUp();
        return false;
      }

    } else {
      //child code
      runChildCode(q, arrays);
    }

  }

  bool SMTLIBSolverImpl::parseSolverOutput(
      const std::vector<const Array*> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
    //open the output from the solver ready to parse
    ifstream file(pathToSolverOutputFile.c_str());

    if (!file.good())
      return false;

    lexer.setInput(file);

    SMTLIBOutputLexer::Token t = SMTLIBOutputLexer::UNRECOGNISED_TOKEN;

    /* The first thing we want to check is if the solver thought the
     * set of assertions was satisfiable
     */
    if (!lexer.getNextToken(t)) {
      klee_warning("SMTLIBSolverImpl: Lexer failed to get token");
      return false;
    }

    switch (t) {
      case SMTLIBOutputLexer::UNKNOWN_TOKEN:
        klee_warning("SMTLIBSolverImpl : Solver responded unknown");
        return false;
      case SMTLIBOutputLexer::UNSAT_TOKEN:
        //not satisfiable
        hasSolution = false;
        return true;
      case SMTLIBOutputLexer::SAT_TOKEN:
        hasSolution = true;
        break;
      default:
        cerr << "SMTLIBSolverImpl : Unexpected token `"
            << lexer.getLastTokenContents() << "`" << endl;
        giveUp();
        return false;
    }

    //If we reach here the solver thought the assertions where satisfiable.
    if (objects.empty()) {
      //we weren't ask to get any values
      return true;
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
            return false;
          }
        }

        // Expect "select"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::SELECT_TOKEN) {
          klee_error(
              "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `select`");
          return false;
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
          return false;
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
          return false;
        }

        //Expect ")"
        if (!lexer.getNextToken(t) || t != SMTLIBOutputLexer::RBRACKET_TOKEN) {
          klee_error(
              "SMTLIBSolverImpl: Lexer failed to get token for array assignment. Expected `)`");
          return false;
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
          return false;
        }

        if (!lexer.getLastNumericValue(determinedByteValue)) {
          klee_error(
              "SMTLIBSolverImpl : Lexer could not get the numeric value of the "
                  "found bitvector constant");
          return false;
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
            return false;
          }
        }

      }

      values.push_back(data);

    }

    //We found satisfiability and determined the array values successfully.
    return true;
  }

  bool SMTLIBSolverImpl::generateSMTLIBv2File(const Query& q,
      const std::vector<const Array*> arrays) {
    //open output SMTLIBv2 file and truncate it
    llvm::raw_fd_ostream output(pathToSolverInputFile.c_str(), ios_base::trunc);

    //check we can write to it
    if (output.has_error()) {
      cerr << "Can't write output SMTLIBv2 (input to solver) "
          << pathToSolverInputFile << endl;
      giveUp();
      return false;
    }

    printer->setOutput(output);
    printer->setQuery(q);
    printer->setArrayValuesToGet(arrays);

    //Generate SMTLIBv2 file containing the query
    printer->generateOutput();

    if (output.has_error()) {
      klee_error("There was a problem writing the SMTLIBv2 file");
      return false;
    }

    output.close();

    if (fileSizeLog != NULL) {
      //Log the size of the file we just made in bytes
      struct stat buf;
      int result = stat(pathToSolverInputFile.c_str(), &buf);
      if (result == -1) {
        perror("stat:");
        return false;
      }

      intmax_t sizeInBytes = buf.st_size;
      *fileSizeLog << stats::queries << " " << sizeInBytes << endl;

    }

    return true;
  }

  bool SMTLIBSolverImpl::haveRunOutOfTime() {
    timespec currentTime;
    timespec elapsedTime;
    if (clock_gettime(CLOCK_MONOTONIC, &currentTime) == -1) {
      cerr << "SMTLIBSolverImpl: Couldn't determine current time!" << endl;
      return true;
    }

    if (timeout.tv_sec == 0)
      return false; //The timeout is disabled, we can never run out of time!

    elapsedTime.tv_sec = (currentTime.tv_sec - startTime.tv_sec) + 1;
    //ignore nanoseconds.
    if (elapsedTime.tv_sec > timeout.tv_sec)
      return true; //we've run out of time.
    else
      return false; //we've got some time left.
  }

  pid_t SMTLIBPipedSolverImpl::solverProcess = 0;

  SMTLIBPipedSolverImpl::SMTLIBPipedSolverImpl(const string& _pathToSolver,
      const string& _pathToOutputTempFile, const string& _pathToInputTempFile) :
      SMTLIBSolverImpl(_pathToSolver, _pathToOutputTempFile,
          _pathToInputTempFile) {
    klee_message("Using SMTLIBPipedSolverImpl");

    //Create the new named pipe that will be used for the duration.
    int result = mkfifo(pathToSolverInputFile.c_str(), 0666);
    if (result == -1) {
      cerr << "Error : Failed to created named pipe "
          << pathToSolverInputFile.c_str() << endl;
      perror("mkfifo:");
      exit (specialExitCode);
    }
  }
  ;

  void SMTLIBPipedSolverImpl::setRecordQueryFileSizes(
      const std::string& logPath) {
    klee_warning("SMTLIBPipedSolverImpl : Cannot log file sizes.");
  }

  void SMTLIBPipedSolverImpl::runChildCode(const Query& q,
      const std::vector<const Array*> arrays) {
    int result = 0;
    solverProcess = 0;

    //Remove the SIGALRM handler, we don't want it!
    signal(SIGALRM, SIG_IGN);

    //Remove KLEE's own signal handlers because we inherited them.
    signal(SIGTERM, SIG_DFL);
    signal(SIGINT, SIG_DFL);
    signal(SIGQUIT, SIG_DFL);

    /* We now fork to setup communication between us and the solver.
     * We flush the stdout and stderr just in case there is anything left in
     * their buffers.
     */
    fflush (stdout);
    fflush (stderr);
    solverProcess = fork();
    if (solverProcess == -1) {
      klee_warning("Failed to fork again in child!");
      exit (specialExitCode);
    }

    if (solverProcess > 0) {
      //Parent code, write SMTLIBv2 query writing to the named pipe

      //If we get killed by the parent we need to clean up any mess we made
      //This should also mean KLEE's original signal handlers don't get called.
      signal(SIGTERM, &(klee::SMTLIBPipedSolverImpl::cleanUpHandler));
      signal(SIGINT, &klee::SMTLIBPipedSolverImpl::cleanUpHandler);
      signal(SIGQUIT, &klee::SMTLIBPipedSolverImpl::cleanUpHandler);

      /* Generate the SMTLIBv2 query. We do it in the child because this process may take a long
       * time and so should be included as part of the timeout.
       */
      if (!generateSMTLIBv2File(q, arrays)) {
        klee_warning("SMTLIBSolverImpl (Child) : Failed to generated query!");
        exit (specialExitCode);
      }

      int status = 0;

      //Now wait for child (the solver) to complete
      do {
        result = waitpid(solverProcess, &status, 0);
      } while (result == -1 && errno == EINTR);

      if (WIFEXITED(status)) {
        if (WEXITSTATUS(status) == specialExitCode) {
          exit (specialExitCode); //something went wrong
        }

        //We're completed properly so exit cleanly like KLEE expects.
        exit(0);
      } else {
        exit (specialExitCode); //something went wrong
      }

    } else {
      //child code, execute the solver reading the named pipe

      //open the output file (truncate it) for the solver and have stdout (of the solver) go into it
      if (freopen(pathToSolverOutputFile.c_str(), "w", stdout) == NULL) {
        klee_error(
            "SMTLIBSolverImpl (Child): Child failed to redirect stdout.");
        exit (specialExitCode);
      }

      /* Invoke the solver. We pass it as the 1st argument the name of SMTLIBv2 file we generated
       * earlier.
       */
      if (execlp(pathToSolver.c_str(), pathToSolver.c_str(),
          pathToSolverInputFile.c_str(), (char*) NULL) == -1) {
        //We failed to invoke the solver
        switch (errno) {
          case ENAMETOOLONG:
            klee_warning(
                "SMTLIBSolverImpl (child of child): The SMTLIBv2 solver path is too long!");
            exit (specialExitCode);
          case ENOENT:
            cerr << "SMTLIBSolverImpl (child of child): The executable "
                << pathToSolver << " does not exist!" << endl;
            exit(specialExitCode);
          default:
            cerr
                << "SMTLIBSolverImpl (child of child): Failed to invoke solver ("
                << pathToSolver << ")" << endl;
            exit(specialExitCode);
        }
      }

    }
  }

  void SMTLIBPipedSolverImpl::cleanUpHandler(int signum) {
    if (solverProcess != 0) {
      cerr << "SMTLIBPipedSolverImpl : Killing and reaping process "
          << solverProcess;
      cerr.flush();
      //Kill the running solver
      kill(solverProcess, SIGKILL);

      //Reap it so there isn't a zombie left behind
      int result = 0;

      do {
        result = waitpid(solverProcess, NULL, 0);
      } while (result == -1);
      cerr << "done" << endl;
    }

    //Now resend ourself the original signal so we exit.
    signal(signum, SIG_DFL);
    kill(getpid(), signum);
  }

  void SMTLIBPipedSolverImpl::performCleanUp() {
    cerr << "SMTLIBPipedSolverImpl: Rebuilding pipe...";
    cerr.flush();
    int result = 0;
    //delete the named pipe because it may have junk in it
    result = unlink(pathToSolverInputFile.c_str());
    if (result == -1) {
      cerr << "Failed to remove old pipe!" << endl;
      perror("unlink:");
    } else {
      //Recreate pipe
      result = mkfifo(pathToSolverInputFile.c_str(), 0666);
      if (result == -1) {
        cerr << "Failed to create new pipe!" << endl;
        perror("mkfifo:");
      }

      cerr << "done" << endl;
    }

  }

}

