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

fn render<'a,N:Label,E:Label,G:Label+GraphWalk<'a,N,E>,W:Writer>(g:&G, w:&W) {
    let writeln = |arg:&[&str]| {
        for &s in arg.iter() {
            w.write_str(s);
        }
        w.write_line("");
    };
    let indented = |arg| { w.write_str("    "); writeln(arg); };

    writeln(["digraph ", g.name().as_slice(), " {"]);
    for &n in g.nodes().iter() {
        indented([n.name().as_slice(), ";"].as_slice());
    }

    let edges : ~[&'a E] = g.edges();
    for &e in edges.iter() {
        let mut escaped_label = e.name().escape_default();
        indented([g.source(e).name().as_slice(), " -> ", g.target(e).name().as_slice(),
                  "[label=\"", escaped_label.as_slice(), "\"];"].as_slice());
    }

    writeln(["}"]);
}
