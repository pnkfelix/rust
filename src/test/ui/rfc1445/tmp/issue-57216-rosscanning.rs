struct SomeStruct {}

fn group_by_shifts<'a, I, J, F>(trips: I, mut on_trip: F)
where
    I: Iterator<Item = (&'a SomeStruct)>,
    J: Iterator<Item = (&'a SomeStruct)>,
    F: FnMut(u32, J),
{
    for g in trips {
        on_trip(123, &g as &Iterator<Item = (&'a SomeStruct)>);
    }
}
