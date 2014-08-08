#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

/// `MinMaxResult` is an enum returned by `min_max`. See `OrdIterator::min_max` for more detail.
pub enum MinMaxResult<T> {
    /// Empty iterator
    NoElements,

    /// Iterator with one element, so the minimum and maximum are the same
    OneElement(T),

    /// More than one element in the iterator, the first element is not larger than the second
    MinMax(T, T)
}

pub trait OrdIterator<A> {
    fn min_max(&mut self) -> MinMaxResult<A>;
}

pub fn foo<A: PartialOrd, T: Iterator<A>>(self_: &mut T) -> MinMaxResult<A> {
    let (mut min, mut max) = match self_.next() {
        None => return NoElements,
        Some(x) => {
            match self_.next() {
                None => return OneElement(x),
                Some(y) => if x < y {(x, y)} else {(y,x)}
            }
        }
    };

    loop {
        // `first` and `second` are the two next elements we want to look at.
        // We first compare `first` and `second` (#1). The smaller one is then compared to
        // current minimum (#2). The larger one is compared to current maximum (#3). This
        // way we do 3 comparisons for 2 elements.
        let first = match self_.next() {
            None => break,
            Some(x) => x
        };
        let second = match self_.next() {
            None => {
                if first < min {
                    min = first;
                } else if first > max {
                    max = first;
                }
                break;
            }
            Some(x) => x
        };
        if first < second {
            if first < min {min = first;}
            if max < second {max = second;}
        } else {
            if second < min {min = second;}
            if max < first {max = first;}
        }
    }

    MinMax(min, max)
}

#[lang="eq"]
pub trait PartialEq {
    /// This method tests for `self` and `other` values to be equal, and is used by `==`.
    fn eq(&self, other: &Self) -> bool;

    /// This method tests for `!=`.
     fn ne(&self, other: &Self) -> bool { !self.eq(other) }
}

#[lang="ord"]
pub trait PartialOrd: PartialEq {
    /// This method returns an ordering between `self` and `other` values
    /// if one exists.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>;

    /// This method tests less than (for `self` and `other`) and is used by the `<` operator.
    fn lt(&self, other: &Self) -> bool {
        match self.partial_cmp(other) {
            Some(Less) => true,
            _ => false,
        }
    }

    /// This method tests less than or equal to (`<=`).
    #[inline]
    fn le(&self, other: &Self) -> bool {
        match self.partial_cmp(other) {
            Some(Less) | Some(Equal) => true,
            _ => false,
        }
    }

    /// This method tests greater than (`>`).
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        match self.partial_cmp(other) {
            Some(Greater) => true,
            _ => false,
        }
    }

    /// This method tests greater than or equal to (`>=`).
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        match self.partial_cmp(other) {
            Some(Greater) | Some(Equal) => true,
            _ => false,
        }
    }
}

#[stable]
pub enum Ordering {
   /// An ordering where a compared value is less [than another].
   Less = -1i,
   /// An ordering where a compared value is equal [to another].
   Equal = 0i,
   /// An ordering where a compared value is greater [than another].
   Greater = 1i,
}

pub enum Option<T> {
    /// No value
    None,
    /// Some value `T`
    Some(T)
}

#[lang="iterator"]
pub trait Iterator<A> {
    /// Advance the iterator and return the next value. Return `None` when the end is reached.
    fn next(&mut self) -> Option<A>;
}
