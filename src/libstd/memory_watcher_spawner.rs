import task::spawn;
import io::println;
import pipes::{stream,Port,Chan};
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

	fn get_memory_watcher_chan() -> comm::Chan<Msg> {

        	let global_memory_watcher_ptr = rustrt::rust_global_memory_watcher_chan_ptr();

        	unsafe {
            		priv::chan_from_global_ptr(global_memory_watcher_ptr, || {
                		task::task().sched_mode(task::SingleThreaded).unlinked()
            		}, global_memory_watcher_spawner)
        	}
    	}

