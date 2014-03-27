use std::io;
use std::vec::Vec;

pub enum LabelText {
    LabelStr(~str),
    EscStr(~str),
}

pub trait Label<Ctxt> {
    // short identifier
    fn name(&self, &Ctxt) -> ~str;

    // descriptive text
    fn text(&self, c:&Ctxt) -> LabelText {
        LabelStr(self.name(c))
    }
}

impl LabelText {
    fn escape_char(c: char, f: |char|) {
        match c {
            '\t' => { f('\\'); f('t'); }
            '\r' => { f('\\'); f('r'); }
            '\n' => { f('\\'); f('n'); }
            // deliberately not escaping \\,
            // since it can be used within escString
            '\'' => { f('\\'); f('\''); }
            '\"'  => { f('\\'); f('\"'); }
            '\x20' .. '\x7e' => { f(c); }
            _ => c.escape_unicode(f),
        }
    }
    fn escaped_str(s: &str) -> ~str {
        use std::str;
        let mut out = str::with_capacity(s.len());
        for c in s.chars() {
            LabelText::escape_char(c, |c| out.push_char(c));
        }
        out
    }

    pub fn escape(&self) -> ~str {
        match self {
            &LabelStr(ref s) => s.escape_default(),
            &EscStr(ref s) => LabelText::escaped_str(*s),
        }
    }
}

// All of the type parameters should be associated items. :(
pub trait GraphWalk<'a, N, E> {
    fn nodes(&self) -> Vec<&'a N>;
    fn edges(&self) -> Vec<&'a E>;
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
        let escaped = n.text(c).escape();
        try!(writeln(w, [n.name(c).as_slice(),
                         "[label=\"", escaped.as_slice(), "\"]",
                         ";"]));
    }

    let edges : Vec<&'a E> = g.edges();
    for &e in edges.iter() {
        let escaped_label = e.text(c).escape();
        try!(w.write_str("    "));
        try!(writeln(w, [g.source(e).name(c).as_slice(), " -> ", g.target(e).name(c).as_slice(),
                         "[label=\"", escaped_label.as_slice(), "\"];"].as_slice()));
    }

    writeln(w, ["}"])
}
