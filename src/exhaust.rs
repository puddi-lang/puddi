//! Pattern exhaustiveness checking (usefulness algorithm).

use crate::ir::{Arm, Lit, Pat, PatKind};
use crate::program::{AdtKind, Program, Shape};
use crate::types::Ty;

#[derive(Clone, Debug, PartialEq)]
enum Ctor {
    Variant(usize),
    Bool(bool),
    Single,
    Lit(String),
    ListExact(usize),
    ListAtLeast(usize),
}

impl Ctor {
    /// Whether a pattern with this constructor can match the candidate.
    fn covers(&self, candidate: &Self) -> bool {
        match (self, candidate) {
            (Self::ListAtLeast(min), Self::ListExact(len) | Self::ListAtLeast(len)) => min <= len,
            _ => self == candidate,
        }
    }
}

#[derive(Clone, Debug)]
enum P {
    Wild,
    C(Ctor, Vec<P>),
}

fn lit_key(l: &Lit) -> String {
    match l {
        Lit::Int(v) => format!("i{v}"),
        Lit::Float(f) => format!("f{f}"),
        Lit::Bool(b) => format!("b{b}"),
        Lit::Char(c) => format!("c{c}"),
        Lit::Str(s) => format!("s{s}"),
        Lit::Unit => "u".into(),
    }
}

/// Convert an IR pattern into its alternatives.
fn convert(prog: &Program, p: &Pat) -> Vec<P> {
    match &p.kind {
        PatKind::Wild => vec![P::Wild],
        PatKind::Bind(_, None) => vec![P::Wild],
        PatKind::Bind(_, Some(sub)) => convert(prog, sub),
        PatKind::Lit(Lit::Bool(b)) => vec![P::C(Ctor::Bool(*b), vec![])],
        PatKind::Lit(Lit::Unit) => vec![P::C(Ctor::Single, vec![])],
        PatKind::Lit(l) => vec![P::C(Ctor::Lit(lit_key(l)), vec![])],
        PatKind::Range(a, b, inc) => vec![P::C(Ctor::Lit(format!("r{}..{}{}", lit_key(a), if *inc { "=" } else { "" }, lit_key(b))), vec![])],
        PatKind::Tuple(ps) => product(prog, ps.iter().collect(), Ctor::Single),
        PatKind::Struct(fs) => {
            let n = match &p.ty {
                Ty::Adt(id, _) => prog.struct_fields(*id).len(),
                _ => fs.len(),
            };
            let pats = fill(fs, n);
            product_opt(prog, pats, Ctor::Single)
        }
        PatKind::Variant(vi, fs) => {
            let n = match &p.ty {
                Ty::Adt(id, _) => match &prog.adts[*id].kind {
                    AdtKind::Enum(vs) => vs[*vi].fields.len(),
                    _ => fs.len(),
                },
                _ => fs.len(),
            };
            let pats = fill(fs, n);
            product_opt(prog, pats, Ctor::Variant(*vi))
        }
        PatKind::Or(ps) => ps.iter().flat_map(|p| convert(prog, p)).collect(),
        PatKind::List(ps, rest) => {
            let ctor = if rest.is_some() { Ctor::ListAtLeast(ps.len()) } else { Ctor::ListExact(ps.len()) };
            product(prog, ps.iter().collect(), ctor)
        }
    }
}

fn fill(fs: &[(usize, Pat)], n: usize) -> Vec<Option<&Pat>> {
    let mut out = vec![None; n];
    for (i, p) in fs {
        if *i < n {
            out[*i] = Some(p);
        }
    }
    out
}

fn product(prog: &Program, ps: Vec<&Pat>, ctor: Ctor) -> Vec<P> {
    product_opt(prog, ps.into_iter().map(Some).collect(), ctor)
}

fn product_opt(prog: &Program, ps: Vec<Option<&Pat>>, ctor: Ctor) -> Vec<P> {
    let mut acc: Vec<Vec<P>> = vec![vec![]];
    for p in ps {
        let alts = match p {
            Some(p) => convert(prog, p),
            None => vec![P::Wild],
        };
        let mut next = Vec::new();
        for a in &acc {
            for alt in &alts {
                let mut v = a.clone();
                v.push(alt.clone());
                next.push(v);
            }
            if next.len() > 4096 {
                break;
            }
        }
        acc = next;
    }
    acc.into_iter().map(|args| P::C(ctor.clone(), args)).collect()
}

fn arity(prog: &Program, ty: &Ty, c: &Ctor) -> usize {
    match c {
        Ctor::Variant(vi) => match ty {
            Ty::Adt(id, _) => match &prog.adts[*id].kind {
                AdtKind::Enum(vs) => vs[*vi].fields.len(),
                _ => 0,
            },
            _ => 0,
        },
        Ctor::Single => match ty {
            Ty::Tuple(ts) => ts.len(),
            Ty::Adt(id, _) => prog.struct_fields(*id).len(),
            _ => 0,
        },
        Ctor::ListExact(n) | Ctor::ListAtLeast(n) => *n,
        _ => 0,
    }
}

fn sub_tys(prog: &Program, ty: &Ty, c: &Ctor) -> Vec<Ty> {
    match (c, ty) {
        (Ctor::Variant(vi), Ty::Adt(id, args)) => match &prog.adts[*id].kind {
            AdtKind::Enum(vs) => vs[*vi].fields.iter().map(|f| prog.normalize_proj(f.ty.subst(args))).collect(),
            _ => vec![],
        },
        (Ctor::Single, Ty::Tuple(ts)) => ts.clone(),
        (Ctor::Single, Ty::Adt(id, args)) => prog.struct_fields(*id).iter().map(|f| prog.normalize_proj(f.ty.subst(args))).collect(),
        (Ctor::ListExact(n) | Ctor::ListAtLeast(n), Ty::Adt(_, args)) => vec![args.first().cloned().unwrap_or(Ty::Error); *n],
        _ => vec![Ty::Error; arity(prog, ty, c)],
    }
}

/// All constructors of a type, if finite.
fn all_ctors(prog: &Program, ty: &Ty, column: &[&P]) -> Option<Vec<Ctor>> {
    match ty {
        Ty::Bool => Some(vec![Ctor::Bool(true), Ctor::Bool(false)]),
        Ty::Unit | Ty::Tuple(_) => Some(vec![Ctor::Single]),
        Ty::Adt(id, _) => {
            if prog.known.get("List").is_some() && *id == prog.known_adt("List") {
                let mut l = 0;
                for p in column {
                    if let P::C(c, _) = p {
                        match c {
                            Ctor::ListExact(n) => l = l.max(n + 1),
                            Ctor::ListAtLeast(n) => l = l.max(*n),
                            _ => {}
                        }
                    }
                }
                let mut v: Vec<Ctor> = (0..l).map(Ctor::ListExact).collect();
                v.push(Ctor::ListAtLeast(l));
                return Some(v);
            }
            match &prog.adts[*id].kind {
                AdtKind::Enum(vs) => Some((0..vs.len()).map(Ctor::Variant).collect()),
                AdtKind::Struct(_) => Some(vec![Ctor::Single]),
            }
        }
        _ => None,
    }
}

/// Specialize a row by constructor `c`; None if the row does not match.
fn specialize(row: &[P], c: &Ctor, n: usize) -> Option<Vec<P>> {
    let (head, rest) = row.split_first()?;
    let mut out = match head {
        P::Wild => vec![P::Wild; n],
        P::C(k, args) if k.covers(c) => {
            let mut fields = args.clone();
            fields.resize(n, P::Wild);
            fields
        }
        P::C(..) => return None,
    };
    out.extend(rest.iter().cloned());
    Some(out)
}

#[derive(Clone, Debug)]
enum W {
    Wild,
    C(Ctor, Ty, Vec<W>),
}

fn useful(prog: &Program, m: &[Vec<P>], q: &[P], tys: &[Ty], depth: u32) -> Option<Vec<W>> {
    if q.is_empty() {
        return if m.is_empty() { Some(vec![]) } else { None };
    }
    if depth > 200 {
        return None;
    }
    let ty = &tys[0];
    match &q[0] {
        P::C(c, _) => {
            let n = arity(prog, ty, c);
            let sm: Vec<Vec<P>> = m.iter().filter_map(|r| specialize(r, c, n)).collect();
            let sq = specialize(q, c, n)?;
            let mut st = sub_tys(prog, ty, c);
            st.extend(tys[1..].iter().cloned());
            let w = useful(prog, &sm, &sq, &st, depth + 1)?;
            let (args, rest) = w.split_at(n);
            let mut out = vec![W::C(c.clone(), ty.clone(), args.to_vec())];
            out.extend(rest.iter().cloned());
            Some(out)
        }
        P::Wild => {
            let column: Vec<&P> = m.iter().filter_map(|r| r.first()).collect();
            let used: Vec<Ctor> = column.iter().filter_map(|p| if let P::C(c, _) = p { Some(c.clone()) } else { None }).collect();
            let all = all_ctors(prog, ty, &column);
            let covered = |c: &Ctor| used.iter().any(|pattern| pattern.covers(c));
            let complete = all.as_ref().is_some_and(|ctors| ctors.iter().all(covered));
            if complete {
                for c in all.unwrap() {
                    let n = arity(prog, ty, &c);
                    let sm: Vec<Vec<P>> = m.iter().filter_map(|r| specialize(r, &c, n)).collect();
                    let mut sq = vec![P::Wild; n];
                    sq.extend(q[1..].iter().cloned());
                    let mut st = sub_tys(prog, ty, &c);
                    st.extend(tys[1..].iter().cloned());
                    if let Some(w) = useful(prog, &sm, &sq, &st, depth + 1) {
                        let (args, rest) = w.split_at(n);
                        let mut out = vec![W::C(c.clone(), ty.clone(), args.to_vec())];
                        out.extend(rest.iter().cloned());
                        return Some(out);
                    }
                }
                None
            } else {
                let d: Vec<Vec<P>> = m.iter().filter(|r| matches!(r.first(), Some(P::Wild))).map(|r| r[1..].to_vec()).collect();
                let w = useful(prog, &d, &q[1..], &tys[1..], depth + 1)?;
                let head = match &all {
                    Some(all) => match all.iter().find(|c| !covered(c)) {
                        Some(c) => {
                            let n = arity(prog, ty, c);
                            W::C(c.clone(), ty.clone(), vec![W::Wild; n])
                        }
                        None => W::Wild,
                    },
                    None => W::Wild,
                };
                let mut out = vec![head];
                out.extend(w);
                Some(out)
            }
        }
    }
}

fn show(prog: &Program, w: &W) -> String {
    match w {
        W::Wild => "_".into(),
        W::C(c, ty, args) => {
            let a: Vec<String> = args.iter().map(|x| show(prog, x)).collect();
            match c {
                Ctor::Bool(b) => b.to_string(),
                Ctor::Lit(s) => s.clone(),
                Ctor::Single => match ty {
                    Ty::Tuple(_) => format!("({})", a.join(", ")),
                    Ty::Unit => "()".into(),
                    Ty::Adt(id, _) => format!("{} {{ .. }}", prog.adts[*id].name),
                    _ => "_".into(),
                },
                Ctor::Variant(vi) => {
                    let Ty::Adt(id, _) = ty else { return "_".into() };
                    let AdtKind::Enum(vs) = &prog.adts[*id].kind else { return "_".into() };
                    let v = &vs[*vi];
                    let prelude_bare = ["Option", "Result"].contains(&prog.adts[*id].name.as_str()) && prog.adts[*id].pkg == crate::program::Pkg::Prelude;
                    let name = if prelude_bare { v.name.clone() } else { format!("{}.{}", prog.adts[*id].name, v.name) };
                    match v.shape {
                        Shape::Unit => name,
                        Shape::Tuple => format!("{name}({})", a.join(", ")),
                        Shape::Record => {
                            let fs: Vec<String> = v.fields.iter().zip(&a).map(|(f, x)| format!("{}: {x}", f.name)).collect();
                            format!("{name} {{ {} }}", fs.join(", "))
                        }
                    }
                }
                Ctor::ListExact(_) => format!("[{}]", a.join(", ")),
                Ctor::ListAtLeast(_) => {
                    let mut v = a.clone();
                    v.push("..".into());
                    format!("[{}]", v.join(", "))
                }
            }
        }
    }
}

pub fn check_match(prog: &Program, ty: &Ty, arms: &[Arm]) -> Result<(), String> {
    let mut rows = Vec::new();
    for a in arms {
        if a.guard.is_some() {
            continue;
        }
        for p in convert(prog, &a.pat) {
            rows.push(vec![p]);
        }
    }
    match useful(prog, &rows, &[P::Wild], std::slice::from_ref(ty), 0) {
        Some(w) => Err(show(prog, &w[0])),
        None => Ok(()),
    }
}

pub fn irrefutable(prog: &Program, p: &Pat) -> bool {
    let rows: Vec<Vec<P>> = convert(prog, p).into_iter().map(|p| vec![p]).collect();
    useful(prog, &rows, &[P::Wild], std::slice::from_ref(&p.ty), 0).is_none()
}
