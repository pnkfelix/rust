trait T0<'a, A> {
    type O;
}

struct L<T> {
    f: T,
}

impl<'a, A, T> T0<'a, A> for L<T>
where
    T: FnMut(A),
{
    type O = T::Output;
}

trait T1: for<'r> Ty<'r> {
    fn m<'a, B: Ty<'a>, F>(&self, f: F) -> ()
    where
        F: for<'r> T0<'r, (<Self as Ty<'r>>::V,), O = <B as Ty<'r>>::V>,
    {
        unimplemented!();
    }
}

trait Ty<'a> {
    type V;
}

fn main() {
    let v = ().m(L{ f : |x|{drop(x)} } );
}

impl<'a> Ty<'a> for () {
    type V = &'a u8;
}

impl T1 for () {}
