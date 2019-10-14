#![feature(async_await, futures_api, generators)]

// A trait with 'static bound
trait MyTrait: 'static {}

async fn foo(b: Box<MyTrait + 'static>) -> () {
    let _bar = b;
    yield
}

pub fn main() {}
