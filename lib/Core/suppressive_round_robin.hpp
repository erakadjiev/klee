/*
 * suppressive_round_robin.hpp
 *
 *  Created on: Feb 26, 2015
 *      Author: rakadjiev
 */

#ifndef SUPPRESSIVE_ROUND_ROBIN_HPP_
#define SUPPRESSIVE_ROUND_ROBIN_HPP_

#include <boost/fiber/algorithm.hpp>
#include <boost/fiber/detail/fifo.hpp>
#include <boost/assert.hpp>

namespace boost {
namespace fibers {

  class suppressive_round_robin : public sched_algorithm{

    private:
      detail::fifo rqueue_;
      fiber_context* suppressed_fiber;
      fiber_context::id suppressed_fiber_id;

    public:
      suppressive_round_robin();
      virtual void awakened(fiber_context*);
      virtual fiber_context* pick_next();
      virtual void set_suppressed_fiber(const fiber_context::id& fiber_id);

  };

  suppressive_round_robin::suppressive_round_robin() : suppressed_fiber(nullptr){}

  void suppressive_round_robin::awakened(fiber_context* f) {
    BOOST_ASSERT(nullptr != f);
    if(f->get_id() == suppressed_fiber_id){
      suppressed_fiber = f;
    } else {
      rqueue_.push(f);
    }
  }

  fiber_context* suppressive_round_robin::pick_next() {
    fiber_context* victim(nullptr);
    if (!rqueue_.empty()) {
      victim = rqueue_.pop();
      BOOST_ASSERT(nullptr != victim);
    } else if (suppressed_fiber != nullptr){
      victim = suppressed_fiber;
      suppressed_fiber = nullptr;
      BOOST_ASSERT(nullptr != victim);
    }
    return victim;
  }

  void suppressive_round_robin::set_suppressed_fiber(const fiber_context::id& fiber_id){
    suppressed_fiber_id = fiber_id;
  }

}
}

#endif /* SUPPRESSIVE_ROUND_ROBIN_HPP_ */
