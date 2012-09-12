import task::spawn;
import io::println;
import pipes::{stream,Port,Chan};
import priv::{chan_from_global_ptr, weaken_task};
import comm = core::comm;
import comm::{Port, Chan, select2, listen};
import task::TaskBuilder;
import either::{Left, Right};

type test1 = {mut x: int, mut y: int};

fn main() {

let oldpoint = {x: 10, y: 20};

let comm_memory_watcher_chan = memory_watcher::get_memory_watcher_chan();

comm_memory_watcher_chan.send(~oldpoint);

}


