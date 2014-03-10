use std::io;

trait Label {
    fn name<'a>(&'a self) -> ~str;
}

// All of the type parameters should be associated items. :(
trait GraphWalk<'a, N, E> {
    fn nodes(&self) -> ~[&'a N];
    fn edges(&self) -> ~[&'a E];
    fn source(&self, edge:&'a E) -> &'a N;
    fn target(&self, edge:&'a E) -> &'a N;
}

type RenderResult = Result<(), io::IoError>;

pub fn render<'a,N:Label,E:Label,G:Label+GraphWalk<'a,N,E>,W:Writer>(g:&G, w:&mut W) -> RenderResult {
    let writeln = |w: &mut W, arg:&[&str]| -> RenderResult {
        for &s in arg.iter() {
            try!(w.write_str(s));
        }
        try!(w.write_line(""));
        Ok(())
    };

    try!(writeln(w, ["digraph ", g.name().as_slice(), " {"]));
    for &n in g.nodes().iter() {
        try!(w.write_str("    "));
        try!(writeln(w, [n.name().as_slice(), ";"]));
    }

    let edges : ~[&'a E] = g.edges();
    for &e in edges.iter() {
        let escaped_label = e.name().escape_default();
        try!(w.write_str("    "));
        try!(writeln(w, [g.source(e).name().as_slice(), " -> ", g.target(e).name().as_slice(),
                         "[label=\"", escaped_label.as_slice(), "\"];"].as_slice()));
    }

    writeln(w, ["}"])
}
