import task::spawn;
import io::println;
import pipes::{stream,Port,Chan};
import priv::{chan_from_global_ptr, weaken_task};
import comm = core::comm;
import comm::{Port, Chan, select2, listen};
import task::TaskBuilder;
import either::{Left, Right};
use std;

extern mod rustrt {
    fn get_global_memory_watcher_chan() -> *libc::uintptr_t;
}

fn main()
{
	const some_value:int = 22;
	let (chan,port) = stream();

	do spawn {
		chan.send(some_value);
		println("Hello");
	}
	
	let monitor_loop_chan_ptr = rustrt::get_global_memory_watcher_chan();
	let test_result = port.recv();
	println(#fmt("%d", test_result));
}
