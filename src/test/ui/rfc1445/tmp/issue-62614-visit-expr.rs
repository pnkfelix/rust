#[derive(PartialEq, Eq)]
struct IAmStructural(u32);
struct NonStructural(u32);

#[derive(PartialEq, Eq)]
struct Wrap<X>(X);

impl PartialEq for NonStructural {
    fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
}

impl Eq for NonStructural { }

const I1: IAmStructural = IAmStructural(1);
const N2: NonStructural = NonStructural(2);
const WI3: Wrap<IAmStructural> = Wrap(IAmStructural(3));
const WN4: Wrap<NonStructural> = Wrap<NonStructural(4));

fn main() {
    
}
