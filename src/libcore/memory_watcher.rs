use task::{spawn,Task};
use io::println;
use pipes::{stream,Port,Chan};
use private::{chan_from_global_ptr, weaken_task};
use comm::{Port, Chan, select2, listen};
use task::TaskBuilder;
use either::{Left, Right};
use send_map::linear;

#[abi = "cdecl"]
extern mod rustrt {
    fn rust_global_memory_watcher_chan_ptr() -> *libc::uintptr_t;
}

pub enum Msg {
        pub ReportAllocation(Task, libc::uintptr_t, *libc::c_char, *libc::c_char)
}

type MemoryWatcherKey = (int, libc::uintptr_t, libc::uintptr_t);

pub fn global_memory_watcher_spawner(msg_po: comm::Port<Msg>)
{
	let msg_received = msg_po.recv();
	let (task_enum_received,size_allocated,td_value,address_allocation) = match msg_received {
  		ReportAllocation(t,s,c,a) => (t,s,c,a)
	};
	
	let mut hm_index:linear::LinearMap<int, @mut linear::LinearMap<libc::uintptr_t, MemoryWatcherKey>> = linear::LinearMap();
	
	loop { 
		match msg_po.recv() { 
			ReportAllocation(t, s, c,a) => {
				let Metrics_value:MemoryWatcherKey = (*(t), s, (c as libc::uintptr_t));
				let test1:int = (*t);
				let val1 = hm_index.find(&test1);
				match val1 {
					Some(T) => {
					let hm_task_LinearMap:@mut linear::LinearMap<libc::uintptr_t, MemoryWatcherKey> = T;
					hm_task_LinearMap.insert((a as libc::uintptr_t), Metrics_value);
					}
					None => {
						let hm_task:@mut linear::LinearMap<libc::uintptr_t, MemoryWatcherKey> = @mut linear::LinearMap();
					hm_task.insert((a as libc::uintptr_t), Metrics_value);
					hm_index.insert(*(t), hm_task);
					}
				}					
			}
		}  
	}

	let remote_task_id = *(task_enum_received);

  	 	

  	let current_task_enum = task::get_task();
  	let current_task_id = *(current_task_enum); 	
  	println(#fmt("Remote task id %d", remote_task_id));
  	println(#fmt("Size value is %d", size_allocated as int));
	
	do spawn {
		println("Hello");
	}
}

pub fn get_memory_watcher_Chan() -> comm::Chan<Msg> {

	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

	unsafe {
		chan_from_global_ptr(global_memory_watcher_ptr, || {
                	task::task().sched_mode(task::SingleThreaded).unlinked()
            	}, global_memory_watcher_spawner)
	}
}

fn memory_watcher_start() {

	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

	unsafe {
		let global_channel = chan_from_global_ptr(global_memory_watcher_ptr, || {
                			task::task().sched_mode(task::SingleThreaded).unlinked()
            				}, global_memory_watcher_spawner);
	}
	println("Memory watcher started");
}

#[test]
fn test_simple() {
let comm_memory_watcher_chan = get_memory_watcher_Chan();

//comm_memory_watcher_chan.send(ReportAllocation(task::get_task()));
let tid_recieve = task::get_task();
let tid = *(tid_recieve);
println(#fmt("current task id %d",tid));
memory_watcher_start();
let box = @0;
}
