//! Recursive-descent parser producing the AST.

use crate::ast::*;
use crate::diag::{Diag, Span};
use crate::lexer::{tok_name, StrPart, Tok, Token};

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    no_struct: bool,
    /// tokens split by `expect_gt`, with their originals, so a failed speculative parse can undo them
    splits: Vec<(usize, Token)>,
}

type PResult<T> = Result<T, Diag>;

pub fn parse_module(toks: Vec<Token>) -> PResult<Module> {
    let mut p = Parser { toks, pos: 0, no_struct: false, splits: Vec::new() };
    p.module()
}

/// Parse a standalone expression from an interpolation token list.
pub fn parse_interp(toks: Vec<Token>) -> PResult<Expr> {
    let mut p = Parser { toks, pos: 0, no_struct: false, splits: Vec::new() };
    let e = p.expr()?;
    if !p.at(&Tok::Eof) {
        return Err(p.unexpected("end of interpolation"));
    }
    Ok(e)
}

impl Parser {
    // ---------- token helpers ----------
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, n: usize) -> &Tok {
        let i = (self.pos + n).min(self.toks.len() - 1);
        &self.toks[i].tok
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn prev_span(&self) -> Span {
        if self.pos == 0 { self.toks[0].span } else { self.toks[self.pos - 1].span }
    }
    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn unexpected(&self, what: &str) -> Diag {
        Diag::new(self.span(), format!("expected {what}, found {}", tok_name(self.peek())))
    }
    fn expect(&mut self, t: &Tok, what: &str) -> PResult<Span> {
        if self.at(t) {
            Ok(self.bump().span)
        } else {
            Err(self.unexpected(what))
        }
    }
    fn skip_nl(&mut self) {
        while self.at(&Tok::Newline) {
            self.bump();
        }
    }
    fn skip_seps(&mut self) {
        while self.at(&Tok::Newline) || self.at(&Tok::Semi) {
            self.bump();
        }
    }
    fn skip_member_seps(&mut self) {
        while self.at(&Tok::Newline) || self.at(&Tok::Semi) || self.at(&Tok::Comma) {
            self.bump();
        }
    }
    fn ident(&mut self) -> PResult<Ident> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                let span = self.bump().span;
                Ok(Ident { name, span })
            }
            _ => Err(self.unexpected("identifier")),
        }
    }
    /// Expect a `>` closing a generic list, splitting `>=` if needed.
    fn expect_gt(&mut self) -> PResult<()> {
        match self.peek() {
            Tok::Gt => {
                self.bump();
                Ok(())
            }
            Tok::Ge => {
                let sp = self.span();
                self.splits.push((self.pos, self.toks[self.pos].clone()));
                self.toks[self.pos].tok = Tok::Assign;
                self.toks[self.pos].span = Span::new(sp.file, sp.lo + 1, sp.hi);
                Ok(())
            }
            _ => Err(self.unexpected("`>`")),
        }
    }

    // ---------- module & items ----------
    fn module(&mut self) -> PResult<Module> {
        let mut imports = Vec::new();
        let mut items = Vec::new();
        loop {
            self.skip_seps();
            if self.at(&Tok::Eof) {
                break;
            }
            if self.at(&Tok::Import) {
                imports.push(self.import()?);
                continue;
            }
            items.push(self.item()?);
        }
        Ok(Module { imports, items })
    }

    fn import(&mut self) -> PResult<Import> {
        let lo = self.expect(&Tok::Import, "`import`")?;
        let first = self.ident()?;
        if self.at(&Tok::Colon) {
            // WIT import: collect raw text until end of line
            let mut text = first.name.clone();
            let mut names = None;
            let mut alias = None;
            while !self.at(&Tok::Newline) && !self.at(&Tok::Eof) && !self.at(&Tok::Semi) {
                if self.at(&Tok::As) {
                    self.bump();
                    alias = Some(self.ident()?);
                    break;
                }
                if self.at(&Tok::Dot) && matches!(self.peek_at(1), Tok::LBrace) {
                    self.bump();
                    self.bump();
                    let mut ns = Vec::new();
                    loop {
                        self.skip_nl();
                        if self.eat(&Tok::RBrace) {
                            break;
                        }
                        ns.push(self.ident()?);
                        self.skip_nl();
                        if !self.eat(&Tok::Comma) {
                            self.skip_nl();
                            self.expect(&Tok::RBrace, "`}`")?;
                            break;
                        }
                    }
                    names = Some(ns);
                    break;
                }
                let t = self.bump();
                match t.tok {
                    Tok::Ident(s) => text.push_str(&s),
                    Tok::Int(n) => text.push_str(&n.to_string()),
                    Tok::Float(f) => text.push_str(&f.to_string()),
                    ref other => text.push_str(crate::lexer::tok_text(other)),
                }
            }
            return Ok(Import { path: vec![first], names, alias, wit: Some(text), span: lo.to(self.prev_span()) });
        }
        let mut path = vec![first];
        let mut names = None;
        while self.eat(&Tok::Dot) {
            if self.at(&Tok::LBrace) {
                self.bump();
                let mut ns = Vec::new();
                loop {
                    self.skip_nl();
                    if self.eat(&Tok::RBrace) {
                        break;
                    }
                    ns.push(self.ident()?);
                    self.skip_nl();
                    if !self.eat(&Tok::Comma) {
                        self.skip_nl();
                        self.expect(&Tok::RBrace, "`}`")?;
                        break;
                    }
                }
                names = Some(ns);
                break;
            }
            path.push(self.ident()?);
        }
        let alias = if self.eat(&Tok::As) { Some(self.ident()?) } else { None };
        Ok(Import { path, names, alias, wit: None, span: lo.to(self.prev_span()) })
    }

    fn attributes(&mut self) -> PResult<Vec<Attribute>> {
        let mut attrs = Vec::new();
        while self.at(&Tok::At) {
            let lo = self.bump().span;
            let name = if self.at(&Tok::Export) {
                let sp = self.bump().span;
                Ident { name: "export".into(), span: sp }
            } else {
                self.ident()?
            };
            let mut args = Vec::new();
            if self.eat(&Tok::LParen) {
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    match self.peek().clone() {
                        Tok::Ident(_) => args.push(AttrArg::Ident(self.ident()?)),
                        Tok::Str(parts) => {
                            let sp = self.bump().span;
                            args.push(AttrArg::Str(plain_string(&parts).ok_or_else(|| Diag::new(sp, "attribute strings cannot use interpolation"))?, sp));
                        }
                        _ => return Err(self.unexpected("attribute argument")),
                    }
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RParen, "`)`")?;
                        break;
                    }
                }
            }
            attrs.push(Attribute { name, args, span: lo.to(self.prev_span()) });
            self.skip_seps();
        }
        Ok(attrs)
    }

    fn item(&mut self) -> PResult<Item> {
        let attrs = self.attributes()?;
        let lo = self.span();
        let vis = if self.eat(&Tok::Pub) {
            Vis::Pub
        } else if self.eat(&Tok::Export) {
            Vis::Export
        } else {
            Vis::Private
        };
        let kind = match self.peek() {
            Tok::Fn | Tok::Async => ItemKind::Fn(self.fn_decl(attrs.clone(), vis != Vis::Private, true)?),
            Tok::Struct => ItemKind::Struct(self.struct_decl()?),
            Tok::Enum => ItemKind::Enum(self.enum_decl()?),
            Tok::Trait => ItemKind::Trait(self.trait_decl()?),
            Tok::Impl => ItemKind::Impl(self.impl_decl()?),
            Tok::Type => {
                self.bump();
                let name = self.ident()?;
                let generics = self.generics()?;
                self.expect(&Tok::Assign, "`=`")?;
                let ty = self.ty()?;
                ItemKind::TypeAlias { name, generics, ty }
            }
            Tok::Const => {
                self.bump();
                let name = self.ident()?;
                self.expect(&Tok::Colon, "`:` and a type")?;
                let ty = self.ty()?;
                self.expect(&Tok::Assign, "`=`")?;
                self.skip_nl();
                let value = self.expr()?;
                ItemKind::Const { name, ty, value }
            }
            Tok::Test => {
                self.bump();
                let name = match self.peek().clone() {
                    Tok::Str(parts) => {
                        let sp = self.bump().span;
                        plain_string(&parts).ok_or_else(|| Diag::new(sp, "test names cannot use interpolation"))?
                    }
                    _ => return Err(self.unexpected("test name string")),
                };
                let body = self.block()?;
                ItemKind::Test { name, body }
            }
            _ => return Err(self.unexpected("item (`fn`, `struct`, `enum`, `trait`, `impl`, `type`, `const`, `test` or `import`)")),
        };
        Ok(Item { attrs, vis, kind, span: lo.to(self.prev_span()) })
    }

    fn generics(&mut self) -> PResult<Vec<GenericParam>> {
        let mut out = Vec::new();
        if !self.eat(&Tok::Lt) {
            return Ok(out);
        }
        loop {
            if self.at(&Tok::Gt) || self.at(&Tok::Ge) {
                self.expect_gt()?;
                break;
            }
            let name = self.ident()?;
            let mut bounds = Vec::new();
            if self.eat(&Tok::Colon) {
                bounds.push(self.ty()?);
                while self.eat(&Tok::Plus) {
                    bounds.push(self.ty()?);
                }
            }
            out.push(GenericParam { name, bounds });
            if !self.eat(&Tok::Comma) {
                self.expect_gt()?;
                break;
            }
        }
        Ok(out)
    }

    fn fn_decl(&mut self, attrs: Vec<Attribute>, is_pub: bool, body_required: bool) -> PResult<std::sync::Arc<FnDecl>> {
        let lo = self.span();
        let is_async = self.eat(&Tok::Async);
        self.expect(&Tok::Fn, "`fn`")?;
        let name = self.ident()?;
        let generics = self.generics()?;
        self.expect(&Tok::LParen, "`(`")?;
        let mut has_self = false;
        let mut params = Vec::new();
        let mut first = true;
        loop {
            if self.eat(&Tok::RParen) {
                break;
            }
            if first && self.at(&Tok::SelfLower) {
                self.bump();
                has_self = true;
            } else {
                let name = match self.peek() {
                    Tok::Underscore => {
                        let sp = self.bump().span;
                        Ident { name: "_".into(), span: sp }
                    }
                    _ => self.ident()?,
                };
                self.expect(&Tok::Colon, "`:` and a parameter type")?;
                let ty = self.ty()?;
                params.push(Param { name, ty });
            }
            first = false;
            if !self.eat(&Tok::Comma) {
                self.expect(&Tok::RParen, "`)`")?;
                break;
            }
        }
        let ret = if self.eat(&Tok::Arrow) { Some(self.ty()?) } else { None };
        let body = if self.at(&Tok::LBrace) {
            Some(self.block()?)
        } else {
            let _ = body_required;
            None
        };
        Ok(std::sync::Arc::new(FnDecl { name, is_async, generics, has_self, params, ret, body, attrs, is_pub, span: lo.to(self.prev_span()) }))
    }

    fn fields(&mut self) -> PResult<Vec<Field>> {
        self.expect(&Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        loop {
            self.skip_member_seps();
            if self.eat(&Tok::RBrace) {
                break;
            }
            let public = self.eat(&Tok::Pub);
            let mutable = self.eat(&Tok::Var);
            let name = self.ident()?;
            self.expect(&Tok::Colon, "`:` and a field type")?;
            let ty = self.ty()?;
            fields.push(Field { name, ty, mutable, public });
            if !(self.at(&Tok::Newline) || self.at(&Tok::Comma) || self.at(&Tok::Semi) || self.at(&Tok::RBrace)) {
                return Err(self.unexpected("`,`, newline or `}` after field"));
            }
        }
        Ok(fields)
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(&Tok::Struct, "`struct`")?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let fields = self.fields()?;
        Ok(StructDecl { name, generics, fields })
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.expect(&Tok::Enum, "`enum`")?;
        let name = self.ident()?;
        let generics = self.generics()?;
        self.expect(&Tok::LBrace, "`{`")?;
        let mut variants = Vec::new();
        loop {
            self.skip_member_seps();
            if self.eat(&Tok::RBrace) {
                break;
            }
            let vname = self.ident()?;
            let kind = if self.eat(&Tok::LParen) {
                let mut tys = Vec::new();
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    tys.push(self.ty()?);
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RParen, "`)`")?;
                        break;
                    }
                }
                VariantKind::Tuple(tys)
            } else if self.at(&Tok::LBrace) {
                VariantKind::Record(self.fields()?)
            } else {
                VariantKind::Unit
            };
            variants.push(Variant { name: vname, kind });
            if !(self.at(&Tok::Newline) || self.at(&Tok::Comma) || self.at(&Tok::Semi) || self.at(&Tok::RBrace)) {
                return Err(self.unexpected("`,`, newline or `}` after variant"));
            }
        }
        Ok(EnumDecl { name, generics, variants })
    }

    fn trait_decl(&mut self) -> PResult<TraitDecl> {
        self.expect(&Tok::Trait, "`trait`")?;
        let name = self.ident()?;
        let generics = self.generics()?;
        let mut supertraits = Vec::new();
        if self.eat(&Tok::Colon) {
            supertraits.push(self.ty()?);
            while self.eat(&Tok::Plus) {
                supertraits.push(self.ty()?);
            }
        }
        self.expect(&Tok::LBrace, "`{`")?;
        let mut assoc_types = Vec::new();
        let mut methods = Vec::new();
        loop {
            self.skip_seps();
            if self.eat(&Tok::RBrace) {
                break;
            }
            if self.eat(&Tok::Type) {
                assoc_types.push(self.ident()?);
                continue;
            }
            let attrs = self.attributes()?;
            methods.push(self.fn_decl(attrs, true, false)?);
        }
        Ok(TraitDecl { name, generics, supertraits, assoc_types, methods })
    }

    fn impl_decl(&mut self) -> PResult<ImplDecl> {
        self.expect(&Tok::Impl, "`impl`")?;
        let generics = if self.at(&Tok::Lt) { self.generics()? } else { Vec::new() };
        let first = self.ty()?;
        let (trait_ref, self_ty) = if self.eat(&Tok::For) { (Some(first), self.ty()?) } else { (None, first) };
        self.expect(&Tok::LBrace, "`{`")?;
        let mut methods = Vec::new();
        let mut assoc_types = Vec::new();
        loop {
            self.skip_seps();
            if self.eat(&Tok::RBrace) {
                break;
            }
            if self.eat(&Tok::Type) {
                let n = self.ident()?;
                self.expect(&Tok::Assign, "`=`")?;
                let t = self.ty()?;
                assoc_types.push((n, t));
                continue;
            }
            let attrs = self.attributes()?;
            let is_pub = self.eat(&Tok::Pub);
            methods.push(self.fn_decl(attrs, is_pub, true)?);
        }
        Ok(ImplDecl { generics, trait_ref, self_ty, methods, assoc_types })
    }

    // ---------- types ----------
    pub fn ty(&mut self) -> PResult<TypeExpr> {
        let lo = self.span();
        match self.peek().clone() {
            Tok::LParen => {
                self.bump();
                let mut tys = Vec::new();
                let mut trailing_comma = false;
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    tys.push(self.ty()?);
                    trailing_comma = false;
                    if self.eat(&Tok::Comma) {
                        trailing_comma = true;
                    } else {
                        self.expect(&Tok::RParen, "`)`")?;
                        break;
                    }
                }
                if tys.len() == 1 && !trailing_comma {
                    return Ok(tys.pop().unwrap());
                }
                Ok(TypeExpr::Tuple(tys, lo.to(self.prev_span())))
            }
            Tok::Fn | Tok::Async => {
                let is_async = self.eat(&Tok::Async);
                self.expect(&Tok::Fn, "`fn`")?;
                self.expect(&Tok::LParen, "`(`")?;
                let mut params = Vec::new();
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    params.push(self.ty()?);
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RParen, "`)`")?;
                        break;
                    }
                }
                let ret = if self.eat(&Tok::Arrow) { Some(Box::new(self.ty()?)) } else { None };
                Ok(TypeExpr::Fn { is_async, params, ret, span: lo.to(self.prev_span()) })
            }
            Tok::Dyn => {
                self.bump();
                let (segs, args) = self.type_path()?;
                Ok(TypeExpr::Dyn { segs, args, span: lo.to(self.prev_span()) })
            }
            Tok::SelfUpper => {
                let sp = self.bump().span;
                if self.at(&Tok::Dot) {
                    let mut segs = vec![Ident { name: "Self".into(), span: sp }];
                    while self.eat(&Tok::Dot) {
                        segs.push(self.ident()?);
                    }
                    return Ok(TypeExpr::Path { segs, args: Vec::new(), span: lo.to(self.prev_span()) });
                }
                Ok(TypeExpr::SelfTy(sp))
            }
            Tok::Ident(_) => {
                let (segs, args) = self.type_path()?;
                Ok(TypeExpr::Path { segs, args, span: lo.to(self.prev_span()) })
            }
            _ => Err(self.unexpected("type")),
        }
    }

    fn type_path(&mut self) -> PResult<(Vec<Ident>, Vec<TypeArg>)> {
        let mut segs = vec![self.ident()?];
        while self.at(&Tok::Dot) && matches!(self.peek_at(1), Tok::Ident(_)) {
            self.bump();
            segs.push(self.ident()?);
        }
        let mut args = Vec::new();
        if self.eat(&Tok::Lt) {
            loop {
                if self.at(&Tok::Gt) || self.at(&Tok::Ge) {
                    self.expect_gt()?;
                    break;
                }
                if matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1) == &Tok::Assign {
                    let n = self.ident()?;
                    self.bump();
                    args.push(TypeArg::Assoc(n, self.ty()?));
                } else {
                    args.push(TypeArg::Type(self.ty()?));
                }
                if !self.eat(&Tok::Comma) {
                    self.expect_gt()?;
                    break;
                }
            }
        }
        Ok((segs, args))
    }

    /// Try to parse `<T, U>` in expression position. Restores position on failure.
    fn try_expr_generic_args(&mut self) -> Option<Vec<TypeExpr>> {
        if !self.at(&Tok::Lt) {
            return None;
        }
        let save = self.pos;
        let mark = self.splits.len();
        let res: PResult<Vec<TypeExpr>> = (|| {
            self.bump();
            let mut args = Vec::new();
            loop {
                args.push(self.ty()?);
                if !self.eat(&Tok::Comma) {
                    if !self.at(&Tok::Gt) {
                        return Err(self.unexpected(">"));
                    }
                    self.bump();
                    break;
                }
            }
            Ok(args)
        })();
        match res {
            Ok(args) if matches!(self.peek(), Tok::LParen | Tok::Dot) || (self.at(&Tok::LBrace) && !self.no_struct) => Some(args),
            _ => {
                // restore any split tokens
                while self.splits.len() > mark {
                    let (i, t) = self.splits.pop().unwrap();
                    self.toks[i] = t;
                }
                self.pos = save;
                None
            }
        }
    }

    // ---------- blocks & statements ----------
    pub fn block(&mut self) -> PResult<Block> {
        let lo = self.expect(&Tok::LBrace, "`{`")?;
        let saved = self.no_struct;
        self.no_struct = false;
        let mut stmts = Vec::new();
        let mut tail = None;
        loop {
            self.skip_seps();
            if self.at(&Tok::RBrace) {
                break;
            }
            if self.at(&Tok::Let) || self.at(&Tok::Var) {
                stmts.push(self.let_stmt()?);
                if !(self.at(&Tok::Newline) || self.at(&Tok::Semi) || self.at(&Tok::RBrace)) {
                    return Err(self.unexpected("newline or `;` after statement"));
                }
                continue;
            }
            let e = self.expr()?;
            self.skip_seps();
            if self.at(&Tok::RBrace) {
                tail = Some(Box::new(e));
                break;
            }
            let prev = &self.toks[self.pos - 1].tok;
            if !(prev == &Tok::Newline || prev == &Tok::Semi || prev == &Tok::RBrace) {
                return Err(self.unexpected("newline or `;` after expression"));
            }
            stmts.push(Stmt::Expr(e));
        }
        let hi = self.expect(&Tok::RBrace, "`}`")?;
        self.no_struct = saved;
        Ok(Block { stmts, tail, span: lo.to(hi) })
    }

    fn let_stmt(&mut self) -> PResult<Stmt> {
        let lo = self.span();
        let mutable = self.bump().tok == Tok::Var;
        let pat = self.pattern()?;
        let ty = if self.eat(&Tok::Colon) { Some(self.ty()?) } else { None };
        self.expect(&Tok::Assign, "`=`")?;
        self.skip_nl();
        let init = self.expr()?;
        let else_block = if self.at(&Tok::Else) {
            self.bump();
            Some(self.block()?)
        } else {
            None
        };
        Ok(Stmt::Let { mutable, pat, ty, init, else_block, span: lo.to(self.prev_span()) })
    }

    // ---------- expressions ----------
    pub fn expr(&mut self) -> PResult<Expr> {
        let lhs = self.range_expr()?;
        let op = match self.peek() {
            Tok::Assign => Some(None),
            Tok::PlusEq => Some(Some(BinOp::Add)),
            Tok::MinusEq => Some(Some(BinOp::Sub)),
            Tok::StarEq => Some(Some(BinOp::Mul)),
            Tok::SlashEq => Some(Some(BinOp::Div)),
            Tok::PercentEq => Some(Some(BinOp::Rem)),
            Tok::AmpEq => Some(Some(BinOp::BitAnd)),
            Tok::PipeEq => Some(Some(BinOp::BitOr)),
            Tok::CaretEq => Some(Some(BinOp::BitXor)),
            Tok::ShlEq => Some(Some(BinOp::Shl)),
            Tok::Gt if self.peek_at(1) == &Tok::Ge && self.adjacent(1) => {
                self.bump();
                Some(Some(BinOp::Shr))
            }
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            self.skip_nl();
            let rhs = self.expr()?;
            let span = lhs.span.to(rhs.span);
            return Ok(Expr { kind: ExprKind::Assign(op, Box::new(lhs), Box::new(rhs)), span });
        }
        Ok(lhs)
    }

    fn adjacent(&self, n: usize) -> bool {
        let a = self.toks[self.pos + n - 1].span;
        let b = self.toks[(self.pos + n).min(self.toks.len() - 1)].span;
        a.hi == b.lo
    }

    fn range_expr(&mut self) -> PResult<Expr> {
        let lhs = self.bin_expr(1)?;
        if self.at(&Tok::DotDot) || self.at(&Tok::DotDotEq) {
            let inclusive = self.bump().tok == Tok::DotDotEq;
            self.skip_nl();
            let rhs = self.bin_expr(1)?;
            let span = lhs.span.to(rhs.span);
            return Ok(Expr { kind: ExprKind::Range(Box::new(lhs), Box::new(rhs), inclusive), span });
        }
        Ok(lhs)
    }

    fn peek_binop(&self) -> Option<(BinOp, u8, usize)> {
        use BinOp::*;
        Some(match self.peek() {
            Tok::PipePipe => (Or, 1, 1),
            Tok::AmpAmp => (And, 2, 1),
            Tok::EqEq => (Eq, 3, 1),
            Tok::Ne => (Ne, 3, 1),
            Tok::Lt => (Lt, 3, 1),
            Tok::Le => (Le, 3, 1),
            Tok::Gt => {
                if self.peek_at(1) == &Tok::Gt && self.adjacent(1) {
                    (Shr, 7, 2)
                } else if self.peek_at(1) == &Tok::Ge && self.adjacent(1) {
                    return None; // `>>=` handled by assignment
                } else {
                    (Gt, 3, 1)
                }
            }
            Tok::Ge => (Ge, 3, 1),
            Tok::Pipe => (BitOr, 4, 1),
            Tok::Caret => (BitXor, 5, 1),
            Tok::Amp => (BitAnd, 6, 1),
            Tok::Shl => (Shl, 7, 1),
            Tok::Plus => (Add, 8, 1),
            Tok::Minus => (Sub, 8, 1),
            Tok::Star => (Mul, 9, 1),
            Tok::Slash => (Div, 9, 1),
            Tok::Percent => (Rem, 9, 1),
            _ => return None,
        })
    }

    fn bin_expr(&mut self, min: u8) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        loop {
            let Some((op, prec, ntoks)) = self.peek_binop() else { break };
            if prec < min {
                break;
            }
            let op_span = self.span();
            for _ in 0..ntoks {
                self.bump();
            }
            self.skip_nl();
            let rhs = self.bin_expr(prec + 1)?;
            if prec == 3 {
                if let Some((_, 3, _)) = self.peek_binop() {
                    return Err(Diag::new(self.span(), "comparison operators cannot be chained; use `&&`").note(format!("first comparison `{}` is here", op.text())));
                }
            }
            let _ = op_span;
            let span = lhs.span.to(rhs.span);
            lhs = Expr { kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let lo = self.span();
        let op = match self.peek() {
            Tok::Minus => Some(UnOp::Neg),
            Tok::Bang => Some(UnOp::Not),
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            let e = self.unary()?;
            let span = lo.to(e.span);
            return Ok(Expr { kind: ExprKind::Unary(op, Box::new(e)), span });
        }
        self.postfix()
    }

    fn is_path_expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Name(..) | ExprKind::SelfType => true,
            ExprKind::Field(b, _, _) => Self::is_path_expr(b),
            _ => false,
        }
    }

    fn path_of(e: &Expr, out: &mut Vec<Ident>) {
        match &e.kind {
            ExprKind::Name(id, _) => out.push(id.clone()),
            ExprKind::SelfType => out.push(Ident { name: "Self".into(), span: e.span }),
            ExprKind::Field(b, id, _) => {
                Self::path_of(b, out);
                out.push(id.clone());
            }
            _ => {}
        }
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut e = self.primary()?;
        loop {
            // a newline followed by `.` continues a method chain
            if self.at(&Tok::Newline) {
                let mut i = self.pos;
                while self.toks[i].tok == Tok::Newline {
                    i += 1;
                }
                if self.toks[i].tok == Tok::Dot {
                    self.pos = i;
                } else {
                    break;
                }
            }
            match self.peek().clone() {
                Tok::Dot => {
                    self.bump();
                    match self.peek().clone() {
                        Tok::Ident(_) => {
                            let id = self.ident()?;
                            let args = self.try_expr_generic_args().unwrap_or_default();
                            let span = e.span.to(self.prev_span());
                            e = Expr { kind: ExprKind::Field(Box::new(e), id, args), span };
                        }
                        Tok::Int(n) => {
                            self.bump();
                            let span = e.span.to(self.prev_span());
                            e = Expr { kind: ExprKind::TupleField(Box::new(e), n as u32), span };
                        }
                        Tok::Await => {
                            self.bump();
                            let span = e.span.to(self.prev_span());
                            e = Expr { kind: ExprKind::Await(Box::new(e)), span };
                        }
                        _ => return Err(self.unexpected("field name, method name or `await` after `.`")),
                    }
                }
                Tok::LParen => {
                    self.bump();
                    let saved = self.no_struct;
                    self.no_struct = false;
                    let mut args = Vec::new();
                    loop {
                        if self.eat(&Tok::RParen) {
                            break;
                        }
                        args.push(self.expr()?);
                        if !self.eat(&Tok::Comma) {
                            self.expect(&Tok::RParen, "`,` or `)`")?;
                            break;
                        }
                    }
                    self.no_struct = saved;
                    let span = e.span.to(self.prev_span());
                    e = Expr { kind: ExprKind::Call(Box::new(e), args), span };
                }
                Tok::LBracket => {
                    self.bump();
                    let saved = self.no_struct;
                    self.no_struct = false;
                    let idx = self.expr()?;
                    self.no_struct = saved;
                    self.expect(&Tok::RBracket, "`]`")?;
                    let span = e.span.to(self.prev_span());
                    e = Expr { kind: ExprKind::Index(Box::new(e), Box::new(idx)), span };
                }
                Tok::Question => {
                    self.bump();
                    let span = e.span.to(self.prev_span());
                    e = Expr { kind: ExprKind::Try(Box::new(e)), span };
                }
                Tok::LBrace if !self.no_struct && Self::is_path_expr(&e) => {
                    let mut path = Vec::new();
                    Self::path_of(&e, &mut path);
                    let args = match &e.kind {
                        ExprKind::Name(_, a) | ExprKind::Field(_, _, a) => a.clone(),
                        _ => Vec::new(),
                    };
                    e = self.struct_lit(path, args, e.span)?;
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn struct_lit(&mut self, path: Vec<Ident>, args: Vec<TypeExpr>, lo: Span) -> PResult<Expr> {
        self.expect(&Tok::LBrace, "`{`")?;
        let saved = self.no_struct;
        self.no_struct = false;
        let mut fields = Vec::new();
        let mut base = None;
        loop {
            self.skip_member_seps();
            if self.eat(&Tok::RBrace) {
                break;
            }
            if self.eat(&Tok::DotDot) {
                base = Some(Box::new(self.expr()?));
                self.skip_member_seps();
                self.expect(&Tok::RBrace, "`}` after struct update base")?;
                break;
            }
            let name = self.ident()?;
            let value = if self.eat(&Tok::Colon) {
                self.skip_nl();
                Some(self.expr()?)
            } else {
                None
            };
            fields.push((name, value));
            if !(self.at(&Tok::Comma) || self.at(&Tok::Newline) || self.at(&Tok::RBrace)) {
                return Err(self.unexpected("`,` or `}` in struct literal"));
            }
        }
        self.no_struct = saved;
        Ok(Expr { kind: ExprKind::Struct { path, args, fields, base }, span: lo.to(self.prev_span()) })
    }

    fn primary(&mut self) -> PResult<Expr> {
        let lo = self.span();
        let mk = |kind, p: &Parser| Expr { kind, span: lo.to(p.prev_span()) };
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(mk(ExprKind::Int(n), self))
            }
            Tok::Float(f) => {
                self.bump();
                Ok(mk(ExprKind::Float(f), self))
            }
            Tok::Char(c) => {
                self.bump();
                Ok(mk(ExprKind::Char(c), self))
            }
            Tok::True => {
                self.bump();
                Ok(mk(ExprKind::Bool(true), self))
            }
            Tok::False => {
                self.bump();
                Ok(mk(ExprKind::Bool(false), self))
            }
            Tok::Str(parts) => {
                self.bump();
                let mut pieces = Vec::new();
                for p in parts {
                    match p {
                        StrPart::Lit(s) => pieces.push(StrPiece::Lit(s)),
                        StrPart::Expr(toks, _) => pieces.push(StrPiece::Expr(parse_interp(toks)?)),
                    }
                }
                Ok(mk(ExprKind::Str(pieces), self))
            }
            Tok::Ident(_) => {
                let id = self.ident()?;
                let args = self.try_expr_generic_args().unwrap_or_default();
                Ok(mk(ExprKind::Name(id, args), self))
            }
            Tok::SelfLower => {
                self.bump();
                Ok(mk(ExprKind::SelfValue, self))
            }
            Tok::SelfUpper => {
                self.bump();
                Ok(mk(ExprKind::SelfType, self))
            }
            Tok::LParen => {
                self.bump();
                let saved = self.no_struct;
                self.no_struct = false;
                if self.eat(&Tok::RParen) {
                    self.no_struct = saved;
                    return Ok(mk(ExprKind::Unit, self));
                }
                let first = self.expr()?;
                if self.eat(&Tok::RParen) {
                    self.no_struct = saved;
                    let mut e = first;
                    e.span = lo.to(self.prev_span());
                    return Ok(e);
                }
                self.expect(&Tok::Comma, "`,` or `)`")?;
                let mut items = vec![first];
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    items.push(self.expr()?);
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RParen, "`,` or `)`")?;
                        break;
                    }
                }
                self.no_struct = saved;
                Ok(mk(ExprKind::Tuple(items), self))
            }
            Tok::LBracket => {
                self.bump();
                let saved = self.no_struct;
                self.no_struct = false;
                if self.eat(&Tok::RBracket) {
                    self.no_struct = saved;
                    return Ok(mk(ExprKind::List(Vec::new()), self));
                }
                if self.at(&Tok::Colon) && self.peek_at(1) == &Tok::RBracket {
                    self.bump();
                    self.bump();
                    self.no_struct = saved;
                    return Ok(mk(ExprKind::Map(Vec::new()), self));
                }
                let first = self.expr()?;
                if self.eat(&Tok::Colon) {
                    let v = self.expr()?;
                    let mut entries = vec![(first, v)];
                    loop {
                        if !self.eat(&Tok::Comma) {
                            self.expect(&Tok::RBracket, "`,` or `]`")?;
                            break;
                        }
                        if self.eat(&Tok::RBracket) {
                            break;
                        }
                        let k = self.expr()?;
                        self.expect(&Tok::Colon, "`:` in map literal")?;
                        let v = self.expr()?;
                        entries.push((k, v));
                    }
                    self.no_struct = saved;
                    return Ok(mk(ExprKind::Map(entries), self));
                }
                let mut items = vec![first];
                loop {
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RBracket, "`,` or `]`")?;
                        break;
                    }
                    if self.eat(&Tok::RBracket) {
                        break;
                    }
                    items.push(self.expr()?);
                }
                self.no_struct = saved;
                Ok(mk(ExprKind::List(items), self))
            }
            Tok::LBrace => {
                let b = self.block()?;
                Ok(mk(ExprKind::Block(b), self))
            }
            Tok::If => self.if_expr(),
            Tok::Match => {
                self.bump();
                let saved = self.no_struct;
                self.no_struct = true;
                let scrut = self.expr()?;
                self.no_struct = saved;
                self.expect(&Tok::LBrace, "`{`")?;
                let saved = self.no_struct;
                self.no_struct = false;
                let mut arms = Vec::new();
                loop {
                    self.skip_member_seps();
                    if self.eat(&Tok::RBrace) {
                        break;
                    }
                    let alo = self.span();
                    let pat = self.pattern()?;
                    let guard = if self.eat(&Tok::If) { Some(self.expr()?) } else { None };
                    self.expect(&Tok::Arrow, "`->` in match arm")?;
                    self.skip_nl();
                    let body = self.expr()?;
                    arms.push(Arm { pat, guard, body, span: alo.to(self.prev_span()) });
                    if !(self.at(&Tok::Comma) || self.at(&Tok::Newline) || self.at(&Tok::Semi) || self.at(&Tok::RBrace)) {
                        return Err(self.unexpected("`,`, newline or `}` after match arm"));
                    }
                }
                self.no_struct = saved;
                Ok(mk(ExprKind::Match { scrut: Box::new(scrut), arms }, self))
            }
            Tok::Loop => {
                self.bump();
                let b = self.block()?;
                Ok(mk(ExprKind::Loop(b), self))
            }
            Tok::While => {
                self.bump();
                let cond = self.cond()?;
                let b = self.block()?;
                Ok(mk(ExprKind::While(cond, b), self))
            }
            Tok::For => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(&Tok::In, "`in`")?;
                let saved = self.no_struct;
                self.no_struct = true;
                let iter = self.expr()?;
                self.no_struct = saved;
                let b = self.block()?;
                Ok(mk(ExprKind::For(pat, Box::new(iter), b), self))
            }
            Tok::Pipe | Tok::PipePipe | Tok::Async => self.closure(),
            Tok::Return => {
                self.bump();
                let v = if self.expr_follows() { Some(Box::new(self.expr()?)) } else { None };
                Ok(mk(ExprKind::Return(v), self))
            }
            Tok::Break => {
                self.bump();
                let v = if self.expr_follows() { Some(Box::new(self.expr()?)) } else { None };
                Ok(mk(ExprKind::Break(v), self))
            }
            Tok::Continue => {
                self.bump();
                Ok(mk(ExprKind::Continue, self))
            }
            _ => Err(self.unexpected("expression")),
        }
    }

    fn expr_follows(&self) -> bool {
        !matches!(self.peek(), Tok::Newline | Tok::Semi | Tok::RBrace | Tok::RParen | Tok::RBracket | Tok::Comma | Tok::Eof)
    }

    fn cond(&mut self) -> PResult<Cond> {
        let saved = self.no_struct;
        self.no_struct = true;
        let c = if self.eat(&Tok::Let) {
            let pat = self.pattern()?;
            self.expect(&Tok::Assign, "`=`")?;
            let e = self.expr()?;
            Cond::Let(pat, Box::new(e))
        } else {
            Cond::Expr(Box::new(self.expr()?))
        };
        self.no_struct = saved;
        Ok(c)
    }

    fn if_expr(&mut self) -> PResult<Expr> {
        let lo = self.expect(&Tok::If, "`if`")?;
        let cond = self.cond()?;
        let then = self.block()?;
        // `else` may start the next line
        let mut i = self.pos;
        while self.toks[i].tok == Tok::Newline {
            i += 1;
        }
        let els = if self.toks[i].tok == Tok::Else {
            self.pos = i;
            self.bump();
            if self.at(&Tok::If) {
                Some(Box::new(self.if_expr()?))
            } else {
                let b = self.block()?;
                let sp = b.span;
                Some(Box::new(Expr { kind: ExprKind::Block(b), span: sp }))
            }
        } else {
            None
        };
        Ok(Expr { kind: ExprKind::If { cond, then, els }, span: lo.to(self.prev_span()) })
    }

    fn closure(&mut self) -> PResult<Expr> {
        let lo = self.span();
        let is_async = self.eat(&Tok::Async);
        let mut params = Vec::new();
        if self.eat(&Tok::PipePipe) {
        } else {
            self.expect(&Tok::Pipe, "`|`")?;
            loop {
                if self.eat(&Tok::Pipe) {
                    break;
                }
                let p = self.pattern_atom()?;
                let t = if self.eat(&Tok::Colon) { Some(self.ty()?) } else { None };
                params.push((p, t));
                if !self.eat(&Tok::Comma) {
                    self.expect(&Tok::Pipe, "`|`")?;
                    break;
                }
            }
        }
        let ret = if self.eat(&Tok::Arrow) { Some(self.ty()?) } else { None };
        let body = if ret.is_some() {
            let b = self.block()?;
            let sp = b.span;
            Expr { kind: ExprKind::Block(b), span: sp }
        } else {
            self.expr()?
        };
        Ok(Expr { kind: ExprKind::Closure { is_async, params, ret, body: Box::new(body) }, span: lo.to(self.prev_span()) })
    }

    // ---------- patterns ----------
    pub fn pattern(&mut self) -> PResult<Pattern> {
        let first = self.pattern_atom()?;
        if !self.at(&Tok::Pipe) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(&Tok::Pipe) {
            self.skip_nl();
            alts.push(self.pattern_atom()?);
        }
        let span = alts[0].span.to(alts.last().unwrap().span);
        Ok(Pattern { kind: PatKind::Or(alts), span })
    }

    fn lit_pat(&mut self) -> PResult<Option<LitPat>> {
        let neg = self.at(&Tok::Minus);
        let off = if neg { 1 } else { 0 };
        let lit = match self.peek_at(off).clone() {
            Tok::Int(n) => {
                let v = n as i128;
                Some(LitPat::Int(if neg { -v } else { v }))
            }
            Tok::Float(f) => Some(LitPat::Float(if neg { -f } else { f })),
            Tok::Char(c) if !neg => Some(LitPat::Char(c)),
            Tok::True if !neg => Some(LitPat::Bool(true)),
            Tok::False if !neg => Some(LitPat::Bool(false)),
            Tok::Str(parts) if !neg => {
                let s = plain_string(&parts).ok_or_else(|| Diag::new(self.span(), "string patterns cannot use interpolation"))?;
                Some(LitPat::Str(s))
            }
            _ => None,
        };
        if lit.is_some() {
            if neg {
                self.bump();
            }
            self.bump();
        }
        Ok(lit)
    }

    fn pattern_atom(&mut self) -> PResult<Pattern> {
        let lo = self.span();
        let mk = |kind, p: &Parser| Pattern { kind, span: lo.to(p.prev_span()) };
        if let Some(l) = self.lit_pat()? {
            if self.at(&Tok::DotDot) || self.at(&Tok::DotDotEq) {
                let inclusive = self.bump().tok == Tok::DotDotEq;
                let Some(h) = self.lit_pat()? else {
                    return Err(self.unexpected("literal for range pattern end"));
                };
                return Ok(mk(PatKind::Range(l, h, inclusive), self));
            }
            return Ok(mk(PatKind::Lit(l), self));
        }
        match self.peek().clone() {
            Tok::Underscore => {
                self.bump();
                Ok(mk(PatKind::Wild, self))
            }
            Tok::LParen => {
                self.bump();
                let mut pats = Vec::new();
                let mut trailing = false;
                loop {
                    if self.eat(&Tok::RParen) {
                        break;
                    }
                    pats.push(self.pattern()?);
                    trailing = false;
                    if self.eat(&Tok::Comma) {
                        trailing = true;
                    } else {
                        self.expect(&Tok::RParen, "`)`")?;
                        break;
                    }
                }
                if pats.len() == 1 && !trailing {
                    let mut p = pats.pop().unwrap();
                    p.span = lo.to(self.prev_span());
                    return Ok(p);
                }
                Ok(mk(PatKind::Tuple(pats), self))
            }
            Tok::LBracket => {
                self.bump();
                let mut pats = Vec::new();
                let mut rest = None;
                loop {
                    if self.eat(&Tok::RBracket) {
                        break;
                    }
                    if self.eat(&Tok::DotDot) {
                        let name = if matches!(self.peek(), Tok::Ident(_)) { Some(self.ident()?) } else { None };
                        rest = Some(name);
                        self.eat(&Tok::Comma);
                        self.expect(&Tok::RBracket, "`]` (a rest pattern must come last)")?;
                        break;
                    }
                    pats.push(self.pattern()?);
                    if !self.eat(&Tok::Comma) {
                        self.expect(&Tok::RBracket, "`,` or `]`")?;
                        break;
                    }
                }
                Ok(mk(PatKind::List(pats, rest), self))
            }
            Tok::Ident(_) | Tok::SelfUpper => {
                let mut path = vec![if self.at(&Tok::SelfUpper) {
                    let sp = self.bump().span;
                    Ident { name: "Self".into(), span: sp }
                } else {
                    self.ident()?
                }];
                while self.at(&Tok::Dot) {
                    self.bump();
                    path.push(self.ident()?);
                }
                if self.eat(&Tok::LParen) {
                    let mut pats = Vec::new();
                    loop {
                        if self.eat(&Tok::RParen) {
                            break;
                        }
                        pats.push(self.pattern()?);
                        if !self.eat(&Tok::Comma) {
                            self.expect(&Tok::RParen, "`)`")?;
                            break;
                        }
                    }
                    return Ok(mk(PatKind::TupleStruct(path, pats), self));
                }
                if self.at(&Tok::LBrace) {
                    self.bump();
                    let mut fields = Vec::new();
                    let mut rest = false;
                    loop {
                        self.skip_member_seps();
                        if self.eat(&Tok::RBrace) {
                            break;
                        }
                        if self.eat(&Tok::DotDot) {
                            rest = true;
                            self.skip_member_seps();
                            self.expect(&Tok::RBrace, "`}`")?;
                            break;
                        }
                        let name = self.ident()?;
                        let p = if self.eat(&Tok::Colon) { Some(self.pattern()?) } else { None };
                        fields.push((name, p));
                        if !(self.at(&Tok::Comma) || self.at(&Tok::Newline) || self.at(&Tok::RBrace)) {
                            return Err(self.unexpected("`,` or `}` in struct pattern"));
                        }
                    }
                    return Ok(mk(PatKind::Struct(path, fields, rest), self));
                }
                if path.len() == 1 {
                    Ok(mk(PatKind::Bind(path.pop().unwrap()), self))
                } else {
                    Ok(mk(PatKind::Path(path), self))
                }
            }
            _ => Err(self.unexpected("pattern")),
        }
    }

}

pub fn plain_string(parts: &[StrPart]) -> Option<String> {
    let mut s = String::new();
    for p in parts {
        match p {
            StrPart::Lit(l) => s.push_str(l),
            StrPart::Expr(..) => return None,
        }
    }
    Some(s)
}
