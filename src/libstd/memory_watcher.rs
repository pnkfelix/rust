import task::spawn;
import io::println;
import pipes::{stream,port,chan};
import priv::{chan_from_global_ptr, weaken_task};
import comm = core::comm;
import comm::{Port, Chan, select2, listen};
import task::TaskBuilder;
import either::{Left, Right};
use std;

#[abi = "cdecl"]
extern mod rustrt {
    fn rust_global_memory_watcher_chan_ptr() -> *libc::uintptr_t;
}

fn global_memory_watcher_spawner()
{
	const some_value:int = 22;
	let (chan,port) = stream();

	do spawn {
		chan.send(some_value);
		println("Hello");
	}
	
	let monitor_loop_chan_ptr = rustrt::rust_global_memory_watcher_chan_ptr();
	let test_result = port.recv();
	println(#fmt("%d", test_result));
}
