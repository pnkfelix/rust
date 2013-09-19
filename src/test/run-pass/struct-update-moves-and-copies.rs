use NC = std::util::NonCopyable;

struct Foo {
    copied: int,
    moved: ~int,
    noncopyable: NC,
}
impl Foo {
    fn new() -> Foo { Foo { copied: 1, moved: ~0, noncopyable: NC } }
}

fn test0(f: Foo, g: NC, h: NC) {
    // just copy implicitly copyable fields from `f`, no moves:
    let b = Foo {moved: ~2, noncopyable: g, ..f};
    let c = Foo {moved: ~3, noncopyable: h, ..f};
    assert_eq!(b.copied, 1);
    assert_eq!(c.copied, 1);
    assert_eq!(f.copied, 1);
    assert_eq!(*f.moved, 0);
}

fn test1(f: Foo, g: NC) {
    // copying move-by-default fields from `f`, so move:
    let b = Foo {noncopyable: g, ..f};
    assert_eq!(b.copied, 1);
    assert_eq!(*b.moved, 0);
}

fn test2(f: Foo) {
    // move non-copyable field
    let _b = Foo {copied: 22, moved: ~23, ..f};
}

fn main() {
    test0(Foo::new(), NC, NC);
    test1(Foo::new(), NC);
    test2(Foo::new());
}
