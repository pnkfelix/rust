import task::{spawn,Task};
import io::println;
import pipes::{stream,Port,Chan};
import priv::{chan_from_global_ptr, weaken_task};
import comm::{Port, Chan, select2, listen};
import task::TaskBuilder;
import either::{Left, Right};
import str::unsafe;

#[abi = "cdecl"]
extern mod rustrt {
    fn rust_global_memory_watcher_chan_ptr() -> *libc::uintptr_t;
}

enum Msg {
        ReportAllocation(Task,libc::uintptr_t,*libc::c_char)
}

fn global_memory_watcher_spawner(msg_po: comm::Port<Msg>)
{
	let msg_received = msg_po.recv();
	let (task_enum_received,size_allocated,td_value) = match msg_received {
  		ReportAllocation(t,s,c) => (t,s,c)
	};

	let remote_task_id = *(task_enum_received);

  	 	

  	let current_task_enum = task::get_task();
  	let current_task_id = *(current_task_enum); 	
  	println(#fmt("Remote task id %d", remote_task_id));
  	println(#fmt("Size value is %d", size_allocated as int));
	unsafe {
		let td_value_str = unsafe::from_c_str(td_value);
		println(#fmt("td_value is %s",td_value_str));
	}
	
	do spawn {
		println("Hello");
	}
}

fn get_memory_watcher_Chan() -> comm::Chan<Msg> {

	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

	unsafe {
		priv::chan_from_global_ptr(global_memory_watcher_ptr, || {
                	task::task().sched_mode(task::SingleThreaded).unlinked()
            	}, global_memory_watcher_spawner)
	}
}

fn memory_watcher_start() {

	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

	unsafe {
		let global_channel = priv::chan_from_global_ptr(global_memory_watcher_ptr, || {
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
