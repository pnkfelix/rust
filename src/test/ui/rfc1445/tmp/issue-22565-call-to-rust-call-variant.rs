use std::panic::AssertUnwindSafe;
fn main() {
    // <Box<_> as FnOnce<((),)>>::call_once(Box::new(|_: ()| { println!("got here"); }), ((),));
    // <FnOnce<((),)>>::call_once(Box::new(|_: ()| { println!("got here"); }), ((),));

    // <Box<_> as FnOnce()>::call_once(Box::new(|_: ()| { println!("got here"); }), ((),))
    (Box::new(|_: ()| { println!("got here"); }))(());
    AssertUnwindSafe(|| { println!("got here"); })();
}
