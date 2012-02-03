fn foo(x: {mutable x: int}, _f: fn@(int)) {
    log(debug, x);
}

fn whoknows(x: @mutable {mutable x: int}, y: int) {
    *x = {mutable x: y};
}

fn main() {
    let box = @mutable {mutable x: 1};
    foo(*box, whoknows(box, _));
    //!^ ERROR may alias with argument
}
