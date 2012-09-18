import task::{spawn,Task};
import io::println;
import pipes::{stream,Port,Chan};
import priv::{chan_from_global_ptr, weaken_task};
import comm::{Port, Chan, select2, listen};
import task::TaskBuilder;
import either::{Left, Right};

#[abi = "cdecl"]
extern mod rustrt {
    fn rust_global_memory_watcher_chan_ptr() -> *libc::uintptr_t;
}

enum Msg {
        ReportAllocation(Task)
}

fn global_memory_watcher_spawner(msg_po: comm::Port<Msg>)
{
	let msg_received = msg_po.recv();
	let task_enum_received = *(msg_received);
	let remote_task_id = *(task_enum_received);
	let current_task_enum = task::get_task();
	let current_task_id = *(current_task_enum);
	if (current_task_id == remote_task_id) {
		println("Memory watcher being called for memory allocated by memory watcher");
		return;
	}
	else {
		println("Values are different");
	}

	println(#fmt("Remote task id %d", remote_task_id));
	println(#fmt("Current task id %d", current_task_id));

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

fn memory_watcher_start()->comm::Chan<Msg> {

	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

	unsafe {
		priv::chan_from_global_ptr(global_memory_watcher_ptr, || {
                	task::task().sched_mode(task::SingleThreaded).unlinked()
            	}, global_memory_watcher_spawner)
	}
}
#[test]
fn test_simple() {
let comm_memory_watcher_chan = get_memory_watcher_Chan();

comm_memory_watcher_chan.send(ReportAllocation(task::get_task()));
let tid_recieve = task::get_task();
let tid = *(tid_recieve);
println(#fmt("current task id %d",tid));
//let box = @0;
}
