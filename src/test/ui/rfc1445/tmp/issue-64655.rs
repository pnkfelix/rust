struct Droppable;

impl Drop for Droppable {
    fn drop(&mut self) {
        println!("Dropping a Droppable");
    }
}

fn main() {
    let _guard = Droppable;
    None::<()>.expect("???");
}
