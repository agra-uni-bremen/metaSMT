#pragma once

#include "concurrent_queue.hpp"

#include <boost/function.hpp>
#include <boost/shared_ptr.hpp>

namespace metaSMT {
  namespace concurrent {


    template<typename Context>
    struct ThreadedWorker {
      typedef boost::function0<void> task_type;
      typedef concurrent_queue< task_type > queue_type;

      boost::shared_ptr<Context> ctx;
      queue_type queue;

      ThreadedWorker( boost::shared_ptr<Context> ctx )
        : ctx(ctx)
          , queue()
      {}

      void operator() () {
        task_type task = NULL;
        while(true) {
          queue.wait_and_pop(task);
          task();
        }
      }
    };

    /**
     * @brief Wrapper for ThreadedWork that is copyable
     **/
    template<typename Context>
    struct ThreadedWorkerWrapper {
      typedef ThreadedWorker<Context> worker_type;
      boost::shared_ptr< worker_type > worker;

      ThreadedWorkerWrapper( boost::shared_ptr<Context> ctx )
        : worker( new worker_type(ctx))
      {}

      void operator() () {
        (*worker)();
      }

      void push( typename worker_type::task_type const & task) {
        worker->queue.push(task);
      }
    };

  } /* namespace concurrent */
} /* namespace metaSMT */

