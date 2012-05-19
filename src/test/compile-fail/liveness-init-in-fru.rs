// -*- rust -*-

type point = {x: int, y: int};

fn main() {
    let mut origin: point;
    origin = {x: 10 with origin}; //! ERROR use of variable that may not have been initialized
}
