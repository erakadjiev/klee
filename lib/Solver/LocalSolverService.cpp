/*
 * LocalSolverService.cpp
 *
 *  Created on: Mar 22, 2015
 *      Author: rakadjiev
 */


#include "LocalSolverService.h"

#include <cstring>
#include <iostream>
#include <fstream>
//#include <regex>
#include <sys/prctl.h>
#include <sys/stat.h>


namespace klee {
  
const int LocalSolverService::num_cpus = sysconf(_SC_NPROCESSORS_ONLN);
const int LocalSolverService::num_solvers = std::max(2, num_cpus - 3);
int LocalSolverService::running_solvers = 0;
zsock_t* LocalSolverService::solver_service = 0;
//std::string LocalSolverService::solver_path = "";
  
solver_proc_info* LocalSolverService::exec_solver(const std::string query){
  fflush(stdout);
  fflush(stderr);
  
  int p2cPipe[2];
  int c2pPipe[2];
  
  if(
      pipe(p2cPipe) ||
      pipe(c2pPipe)){
    std::cerr << "Failed to pipe\n";
    return NULL;
  }
  
  pid_t pid = fork();
  if (pid > 0) {
    // parent
    close(p2cPipe[0]);
    close(c2pPipe[1]);
    
    int ret = write(p2cPipe[1], query.c_str(), query.length()+1);
    close(p2cPipe[1]);
    
    return new solver_proc_info(pid, c2pPipe[0]);
  }
  else if (pid == 0) {
    // child
    
    // Terminate child if parent dies (works only in Linux)
    prctl(PR_SET_PDEATHSIG, SIGTERM);
    
    if(dup2(p2cPipe[0], STDIN_FILENO) == -1 ||
        dup2(c2pPipe[1], STDOUT_FILENO) == -1 ||
        dup2(c2pPipe[1], STDERR_FILENO) == -1){
      std::cerr << "Failed to redirect stdin/stdout/stderr\n";
      exit(1);
    }
    close(p2cPipe[0]);
    close(p2cPipe[1]);
    close(c2pPipe[0]);
    close(c2pPipe[1]);
    
    int ret = execl("/home/rakadjiev/workspace/stpwrap2/build/stpwrap2", "/home/rakadjiev/workspace/stpwrap2/build/stpwrap2", (char*)NULL);
    exit(ret);
  }
  else {
    std::cerr << "Failed to fork!\n";
    return NULL;
  }
}

int LocalSolverService::solver_result_handler(zloop_t* reactor, zmq_pollitem_t* child_pipe, void* arg){
  int fd = child_pipe->fd;
  int readBytes = 1;
  char buf[100];
  std::string ans;
  
  while((readBytes = read(fd, buf, sizeof(buf)-1)) > 0){
    ans.append(buf, readBytes);
  }
  
  zloop_poller_end(reactor, child_pipe);
  close(fd);
  solver_reply_info* rep = (solver_reply_info*)arg;
  
  unsigned short solver_status = 0;
  
  int status;
  pid_t res = waitpid(rep->pid, &status, WNOHANG | WUNTRACED);
  
  if (res < 0) {
    std::cerr << "ERROR: waitpid() for STP failed";
    solver_status = 3;
  }
  
  // From timed_run.py: It appears that linux at least will on
  // "occasion" return a status when the process was terminated by a
  // signal, so test signal first.
  if (WIFSIGNALED(status) || !WIFEXITED(status)) {
    std::cerr << "error: STP did not return successfully.  Most likely you forgot to run 'ulimit -s unlimited'\n";
    std::cerr << WIFSIGNALED(status) << " " << WTERMSIG(status) << "\n";
    std::cerr << WIFEXITED(status) << "\n";
    solver_status = 3;
  }
  
  int exitcode = WEXITSTATUS(status);
  if (exitcode==0) {
    // has solution
    solver_status = 0;
  } else if (exitcode==1) {
    // doesn't have solution
    solver_status = 1;
  } else if (exitcode==52) {
    // timeout
    std::cerr << "STP timed out";
    solver_status = 2;
  } else {
    // some problem
    std::cerr << "error: STP did not return a recognized code (" << exitcode << ")\n";
    std::cerr << ans << "\n";
    solver_status = 3;
  }
  
  --running_solvers;
  if(running_solvers == num_solvers-1){
    zloop_reader(reactor, solver_service, solver_handler, NULL);
    //  std::cout << "Some solvers are ready, continuing to accept queries.\n";
  }
  
  zmsg_t* ans_msg = zmsg_new();
  zmsg_addstr(ans_msg, rep->message_id.c_str());
  zmsg_addstr(ans_msg, std::to_string(solver_status).c_str());
  if(solver_status == 0){
    zmsg_addstr(ans_msg, ans.c_str());
  }
  zmsg_send(&ans_msg, solver_service);
//  std::cout << "Sent solver_service answer\n";
  delete rep;
  
  return 0;
}

int LocalSolverService::solver_handler(zloop_t* reactor, zsock_t* solver_service, void *arg){
  zmsg_t* msg = zmsg_recv(solver_service);
  char* id = zmsg_popstr(msg);
  if (std::strcmp(id, "$TERM") == 0){
    zstr_free(&id);
    zmsg_destroy(&msg);
    //end the reactor
//    std::cout << "Received $TERM. Stopping the reactor.\n";
    return -1;
  } else {
    char* que = zmsg_popstr(msg);
    zmsg_destroy(&msg);
//    std::cout << "Received solver_service query\n";
    
    solver_proc_info* proc = exec_solver(que);
    zstr_free(&que);
    
    zmq_pollitem_t child_pipe;
    child_pipe.socket = NULL;
    child_pipe.fd = proc->fd;
    child_pipe.events = ZMQ_POLLIN;
    
    solver_reply_info* rep = new solver_reply_info(proc->pid, id);
    zstr_free(&id);
    delete proc;
    
    zloop_poller(reactor, &child_pipe, solver_result_handler, rep);
    
    ++running_solvers;
    if(running_solvers >= num_solvers){
      zloop_reader_end(reactor, solver_service);
      //  std::cout << "All solvers busy, not accepting more queries.\n";
    }
    
    return 0;
  }
}

void LocalSolverService::solver_actor (zsock_t* pipe, void* arg){
  solver_service = pipe;
//  solver_path = *((std::string*)arg);
  // Required initialization
  zsock_signal (pipe, 0);
  zloop_t* reactor = zloop_new();
  zloop_reader(reactor, solver_service, solver_handler, NULL);
  zloop_start(reactor);
  
  zloop_destroy(&reactor);
//  std::cout << "Solver service exiting...\n";
}

}
