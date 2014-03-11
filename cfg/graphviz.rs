use std::io;

pub trait Label<Ctxt> {
    // short identifier
    fn name(&self, &Ctxt) -> ~str;

    // descriptive text
    fn text(&self, c:&Ctxt) -> ~str {
        self.name(c)
    }
}

// All of the type parameters should be associated items. :(
pub trait GraphWalk<'a, N, E> {
    fn nodes(&self) -> ~[&'a N];
    fn edges(&self) -> ~[&'a E];
    fn source(&self, edge:&'a E) -> &'a N;
    fn target(&self, edge:&'a E) -> &'a N;
}

pub type RenderResult = Result<(), io::IoError>;

pub fn render<'a,C,N:Label<C>,E:Label<C>,G:Label<C>+GraphWalk<'a,N,E>,W:Writer>(
    c: &C,
    g: &G,
    w: &mut W) -> RenderResult
{
    let writeln = |w: &mut W, arg:&[&str]| -> RenderResult {
        for &s in arg.iter() {
            try!(w.write_str(s));
        }
        try!(w.write_line(""));
        Ok(())
    };

    try!(writeln(w, ["digraph ", g.name(c).as_slice(), " {"]));
    for &n in g.nodes().iter() {
        try!(w.write_str("    "));
        try!(writeln(w, [n.name(c).as_slice(),
                         "[label=\"", n.text(c).escape_default().as_slice(), "\"]",
                         ";"]));
    }

    let edges : ~[&'a E] = g.edges();
    for &e in edges.iter() {
        let escaped_label = e.text(c).escape_default();
        try!(w.write_str("    "));
        try!(writeln(w, [g.source(e).name(c).as_slice(), " -> ", g.target(e).name(c).as_slice(),
                         "[label=\"", escaped_label.as_slice(), "\"];"].as_slice()));
    }

    writeln(w, ["}"])
}
