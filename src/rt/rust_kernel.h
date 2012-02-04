// -*- c++ -*-
#ifndef RUST_KERNEL_H
#define RUST_KERNEL_H

#include <map>
#include "memory_region.h"
#include "rust_log.h"

struct rust_task_thread;
struct rust_scheduler;

typedef hash_map<rust_task_id, rust_task *> task_map;
typedef std::map<rust_sched_id, rust_scheduler *> sched_map;

/**
 * A global object shared by all thread domains. Most of the data structures
 * in this class are synchronized since they are accessed from multiple
 * threads.
 */
class rust_kernel {
    memory_region _region;
    rust_log _log;

public:
    rust_srv *srv;
private:

    // Protects live_tasks, max_task_id and task_table
    lock_and_signal task_lock;
    // Tracks the number of tasks that are being managed by
    // schedulers. When this hits 0 we will tell all schedulers
    // to exit.
    uintptr_t live_tasks;
    // The next task id
    rust_task_id max_task_id;
    task_map task_table;

    // Potects max_sched_id and sched_table
    lock_and_signal sched_lock;
    // Tracks the number of schedulers that are running. When this
    // hits zero the kernel will exit.
    uintptr_t live_schedulers;
    rust_sched_id max_sched_id;
    sched_map sched_table;

    lock_and_signal rval_lock;
    int rval;

    void tell_schedulers_to_exit();

public:

    struct rust_env *env;

    rust_kernel(rust_srv *srv);
    ~rust_kernel();

    void log(uint32_t level, char const *fmt, ...);
    void fatal(char const *fmt, ...);

    void *malloc(size_t size, const char *tag);
    void *realloc(void *mem, size_t size);
    void free(void *mem);

    void fail();

    rust_sched_id create_scheduler(size_t num_threads);
    rust_scheduler *get_scheduler_by_id(rust_sched_id id);
    void release_scheduler_id(rust_sched_id id);

#ifdef __WIN32__
    void win32_require(LPCTSTR fn, BOOL ok);
#endif

    void register_task(rust_task *task);
    rust_task *get_task_by_id(rust_task_id id);
    void release_task_id(rust_task_id tid);

    void set_exit_status(int code);

    int wait_on_schedulers();
};

#endif /* RUST_KERNEL_H */
