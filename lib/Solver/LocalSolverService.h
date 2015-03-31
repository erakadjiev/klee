/*
 * LocalSolverService.h
 *
 *  Created on: Mar 22, 2015
 *      Author: rakadjiev
 */

#ifndef LIB_SOLVER_LOCALSOLVERSERVICE_H_
#define LIB_SOLVER_LOCALSOLVERSERVICE_H_

#include <czmq.h>
#include <string>
#include <algorithm>
#include <unistd.h>

namespace klee{
  
  struct solver_reply_info{
  public:
   explicit solver_reply_info(int _pid, std::string _message_id) :
    pid(_pid), message_id(_message_id){}
   int pid;
   std::string message_id;
  };
  
  struct solver_proc_info{
  public:
   explicit solver_proc_info(int _pid, int _fd) :
    pid(_pid), fd(_fd){}
   int pid;
   int fd;
  };
  
  class LocalSolverService{
    private:
      static zsock_t* solver_service;
//      static std::string solver_path;
      // this is number of logical CPUs, getting physical cores seems more difficult
      static const int num_cpus;
      static const int num_solvers;
      static int running_solvers;
      static solver_proc_info* exec_solver(const std::string query);
      static int solver_result_handler(zloop_t* reactor, zmq_pollitem_t* child_pipe, void* arg);
      static int solver_handler(zloop_t* reactor, zsock_t* solver_service, void *arg);
    public:
      static void solver_actor(zsock_t* pipe, void* arg);
  };
}




#endif /* LIB_SOLVER_LOCALSOLVERSERVICE_H_ */
