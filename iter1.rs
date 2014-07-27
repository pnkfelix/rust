#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub trait GreaterThan { fn gt(&self, that: &Self) -> bool; }

pub enum Option<T> {
    /// No value
    None,
    /// Some value `T`
    Some(T)
}

impl<T> Option<T> {
    pub fn map<U>(self, f: |T| -> U) -> Option<U> {
        match self { Some(x) => Some(f(x)), None => None }
    }
}

pub trait Iterator<A> {
    fn fold<B>(&mut self, init: B, f: |B, A| -> B) -> B;

    #[inline]
    // originally named `max_by`
    fn max_by<B: GreaterThan>(&mut self, f: |&A| -> B) -> Option<A> {
        fn foo<A,B: GreaterThan>(f: |&A| -> B,
                                 max: Option<(A, B)>,
                                 x: A) -> Option<(A, B)> {
            let x_val = f(&x);
            match max {
                None             => Some((x, x_val)),
                Some((y, y_val)) => if x_val.gt(&y_val) {
                    drop((y, y_val));
                    Some((x, x_val))
                } else {
                    drop((x, x_val));
                    Some((y, y_val))
                }
            }
        }

        self.fold(None, |max: Option<(A, B)>, x| foo(|a|f(a), max, x))
            .map(|(x, _)| x)
    }
}
