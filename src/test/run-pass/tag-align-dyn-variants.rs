tag a_tag<A,B> {
    varA(A);
    varB(B);
}

type t_rec<A,B> = {
    chA: u8,
    tA: a_tag<A,B>,
    chB: u8,
    tB: a_tag<A,B>
};

fn mk_rec<A,B>(a: A, b: B) -> t_rec {
    ret { chA:0u8, tA:varA(a), chB:1u8, tB:varB(b) };
}

fn is_8_byte_aligned(&&u: a_tag) -> bool {
    let p = ptr::addr_of(u) as uint;
    ret (p & 7u) == 0u;
}

fn is_4_byte_aligned(&&u: a_tag) -> bool {
    let p = ptr::addr_of(u) as uint;
    ret (p & 3u) == 0u;
}

fn main() {
    let x = mk_rec(22u64, 23u64);
    assert is_8_byte_aligned(x.tA);
    assert is_8_byte_aligned(x.tB);

    let x = mk_rec(22u64, 23u32);
    assert is_8_byte_aligned(x.tA);
    assert is_8_byte_aligned(x.tB);

    let x = mk_rec(22u32, 23u64);
    assert is_8_byte_aligned(x.tA);
    assert is_8_byte_aligned(x.tB);

    let x = mk_rec(22u32, 23u32);
    assert is_4_byte_aligned(x.tA);
    assert is_4_byte_aligned(x.tB);
}
