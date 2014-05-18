// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast;
use codemap::{Span, respan};
use ext::base::*;
use ext::base;
use ext::build::AstBuilder;
use parse::token::InternedString;
use parse::token;
use ptr::P;
use rsparse = parse;

use parse = fmt_macros;
use collections::{HashMap, HashSet};

#[deriving(Eq)]
enum ArgumentType {
    Known(StrBuf),
    Unsigned,
    String,
}

enum Position {
    Exact(uint),
    Named(StrBuf),
}

struct Context<'a, 'b> {
    ecx: &'a mut ExtCtxt<'b>,
    fmtsp: Span,

    // Parsed argument expressions and the types that we've found so far for
    // them.
    args: Vec<P<ast::Expr>>,
    arg_types: Vec<Option<ArgumentType>>,
    // Parsed named expressions and the types that we've found for them so far.
    // Note that we keep a side-array of the ordering of the named arguments
    // found to be sure that we can translate them in the same order that they
    // were declared in.
    names: HashMap<StrBuf, P<ast::Expr>>,
    name_types: HashMap<StrBuf, ArgumentType>,
    name_ordering: Vec<StrBuf>,

    // Collection of the compiled `rt::Piece` structures
    pieces: Vec<P<ast::Expr>> ,
    name_positions: HashMap<StrBuf, uint>,
    method_statics: Vec<P<ast::Item>> ,

    // Updated as arguments are consumed or methods are entered
    nest_level: uint,
    next_arg: uint,
}

pub enum Invocation {
    Call(P<ast::Expr>),
    MethodCall(P<ast::Expr>, ast::Ident),
}

/// Parses the arguments from the given list of tokens, returning None
/// if there's a parse error so we can continue parsing other format!
/// expressions.
///
/// If parsing succeeds, the second return value is:
///
///     Some((fmtstr, unnamed arguments, ordering of named arguments,
///           named arguments))
fn parse_args(ecx: &mut ExtCtxt, sp: Span, allow_method: bool,
              tts: &[ast::TokenTree])
    -> (Invocation, Option<(P<ast::Expr>, Vec<P<ast::Expr>>, Vec<StrBuf>,
                            HashMap<StrBuf, P<ast::Expr>>)>) {
    let mut args = Vec::new();
    let mut names = HashMap::<StrBuf, P<ast::Expr>>::new();
    let mut order = Vec::new();

    let mut p = rsparse::new_parser_from_tts(ecx.parse_sess(),
                                             ecx.cfg(),
                                             tts.iter()
                                                .map(|x| (*x).clone())
                                                .collect());
    // Parse the leading function expression (maybe a block, maybe a path)
    let invocation = if allow_method {
        let e = p.parse_expr();
        if !p.eat(&token::COMMA) {
            ecx.span_err(sp, "expected token: `,`");
            return (Call(e), None);
        }
        MethodCall(e, p.parse_ident())
    } else {
        Call(p.parse_expr())
    };
    if !p.eat(&token::COMMA) {
        ecx.span_err(sp, "expected token: `,`");
        return (invocation, None);
    }

    if p.token == token::EOF {
        ecx.span_err(sp, "requires at least a format string argument");
        return (invocation, None);
    }
    let fmtstr = p.parse_expr();
    let mut named = false;
    while p.token != token::EOF {
        if !p.eat(&token::COMMA) {
            ecx.span_err(sp, "expected token: `,`");
            return (invocation, None);
        }
        if p.token == token::EOF { break } // accept trailing commas
        if named || (token::is_ident(&p.token) &&
                     p.look_ahead(1, |t| *t == token::EQ)) {
            named = true;
            let ident = match p.token {
                token::IDENT(i, _) => {
                    p.bump();
                    i
                }
                _ if named => {
                    ecx.span_err(p.span,
                                 "expected ident, positional arguments \
                                 cannot follow named arguments");
                    return (invocation, None);
                }
                _ => {
                    ecx.span_err(p.span,
                                 format!("expected ident for named argument, but found `{}`",
                                         p.this_token_to_str()));
                    return (invocation, None);
                }
            };
            let interned_name = token::get_ident(ident);
            let name = interned_name.get();
            p.expect(&token::EQ);
            let e = p.parse_expr();
            match names.find_equiv(&name) {
                None => {}
                Some(prev) => {
                    ecx.span_err(e.span, format!("duplicate argument named `{}`", name));
                    ecx.parse_sess.span_diagnostic.span_note(prev.span, "previously here");
                    continue
                }
            }
            order.push(name.to_strbuf());
            names.insert(name.to_strbuf(), e);
        } else {
            args.push(p.parse_expr());
        }
    }
    return (invocation, Some((fmtstr, args, order, names)));
}

impl<'a, 'b> Context<'a, 'b> {
    /// Verifies one piece of a parse string. All errors are not emitted as
    /// fatal so we can continue giving errors about this and possibly other
    /// format strings.
    fn verify_piece(&mut self, p: &parse::Piece) {
        match *p {
            parse::String(..) => {}
            parse::CurrentArgument => {
                if self.nest_level == 0 {
                    self.ecx.span_err(self.fmtsp,
                                      "`#` reference used with nothing to \
                                       reference back to");
                }
            }
            parse::Argument(ref arg) => {
                // width/precision first, if they have implicit positional
                // parameters it makes more sense to consume them first.
                self.verify_count(arg.format.width);
                self.verify_count(arg.format.precision);

                // argument second, if it's an implicit positional parameter
                // it's written second, so it should come after width/precision.
                let pos = match arg.position {
                    parse::ArgumentNext => {
                        let i = self.next_arg;
                        if self.check_positional_ok() {
                            self.next_arg += 1;
                        }
                        Exact(i)
                    }
                    parse::ArgumentIs(i) => Exact(i),
                    parse::ArgumentNamed(s) => Named(s.to_strbuf()),
                };

                // and finally the method being applied
                match arg.method {
                    None => {
                        let ty = Known(arg.format.ty.to_strbuf());
                        self.verify_arg_type(pos, ty);
                    }
                    Some(ref method) => { self.verify_method(pos, *method); }
                }
            }
        }
    }

    fn verify_pieces(&mut self, pieces: &[parse::Piece]) {
        for piece in pieces.iter() {
            self.verify_piece(piece);
        }
    }

    fn verify_count(&mut self, c: parse::Count) {
        match c {
            parse::CountImplied | parse::CountIs(..) => {}
            parse::CountIsParam(i) => {
                self.verify_arg_type(Exact(i), Unsigned);
            }
            parse::CountIsName(s) => {
                self.verify_arg_type(Named(s.to_strbuf()), Unsigned);
            }
            parse::CountIsNextParam => {
                if self.check_positional_ok() {
                    self.verify_arg_type(Exact(self.next_arg), Unsigned);
                    self.next_arg += 1;
                }
            }
        }
    }

    fn check_positional_ok(&mut self) -> bool {
        if self.nest_level != 0 {
            self.ecx.span_err(self.fmtsp, "cannot use implicit positional \
                                           arguments nested inside methods");
            false
        } else {
            true
        }
    }

    fn verify_method(&mut self, pos: Position, m: &parse::Method) {
        self.nest_level += 1;
        match *m {
            parse::Plural(_, ref arms, ref default) => {
                let mut seen_cases = HashSet::new();
                self.verify_arg_type(pos, Unsigned);
                for arm in arms.iter() {
                    if !seen_cases.insert(arm.selector) {
                        match arm.selector {
                            parse::Keyword(name) => {
                                self.ecx.span_err(self.fmtsp,
                                                  format!("duplicate selector \
                                                           `{}`", name));
                            }
                            parse::Literal(idx) => {
                                self.ecx.span_err(self.fmtsp,
                                                  format!("duplicate selector \
                                                           `={}`", idx));
                            }
                        }
                    }
                    self.verify_pieces(arm.result.as_slice());
                }
                self.verify_pieces(default.as_slice());
            }
            parse::Select(ref arms, ref default) => {
                self.verify_arg_type(pos, String);
                let mut seen_cases = HashSet::new();
                for arm in arms.iter() {
                    if !seen_cases.insert(arm.selector) {
                        self.ecx.span_err(self.fmtsp,
                                          format!("duplicate selector `{}`",
                                               arm.selector));
                    } else if arm.selector == "" {
                        self.ecx.span_err(self.fmtsp,
                                          "empty selector in `select`");
                    }
                    self.verify_pieces(arm.result.as_slice());
                }
                self.verify_pieces(default.as_slice());
            }
        }
        self.nest_level -= 1;
    }

    fn verify_arg_type(&mut self, arg: Position, ty: ArgumentType) {
        match arg {
            Exact(arg) => {
                if self.args.len() <= arg {
                    let msg = format!("invalid reference to argument `{}` (there \
                                    are {} arguments)", arg, self.args.len());
                    self.ecx.span_err(self.fmtsp, msg);
                    return;
                }
                {
                    let arg_type = match self.arg_types.get(arg) {
                        &None => None,
                        &Some(ref x) => Some(x)
                    };
                    self.verify_same(self.args.get(arg).span, &ty, arg_type);
                }
                if self.arg_types.get(arg).is_none() {
                    *self.arg_types.get_mut(arg) = Some(ty);
                }
            }

            Named(name) => {
                let span = match self.names.find(&name) {
                    Some(e) => e.span,
                    None => {
                        let msg = format!("there is no argument named `{}`", name);
                        self.ecx.span_err(self.fmtsp, msg);
                        return;
                    }
                };
                self.verify_same(span, &ty, self.name_types.find(&name));
                if !self.name_types.contains_key(&name) {
                    self.name_types.insert(name.clone(), ty);
                }
                // Assign this named argument a slot in the arguments array if
                // it hasn't already been assigned a slot.
                if !self.name_positions.contains_key(&name) {
                    let slot = self.name_positions.len();
                    self.name_positions.insert(name, slot);
                }
            }
        }
    }

    /// When we're keeping track of the types that are declared for certain
    /// arguments, we assume that `None` means we haven't seen this argument
    /// yet, `Some(None)` means that we've seen the argument, but no format was
    /// specified, and `Some(Some(x))` means that the argument was declared to
    /// have type `x`.
    ///
    /// Obviously `Some(Some(x)) != Some(Some(y))`, but we consider it true
    /// that: `Some(None) == Some(Some(x))`
    fn verify_same(&self,
                   sp: Span,
                   ty: &ArgumentType,
                   before: Option<&ArgumentType>) {
        let cur = match before {
            None => return,
            Some(t) => t,
        };
        if *ty == *cur {
            return
        }
        match (cur, ty) {
            (&Known(ref cur), &Known(ref ty)) => {
                self.ecx.span_err(sp,
                                  format!("argument redeclared with type `{}` when \
                                           it was previously `{}`",
                                          *ty,
                                          *cur));
            }
            (&Known(ref cur), _) => {
                self.ecx.span_err(sp,
                                  format!("argument used to format with `{}` was \
                                           attempted to not be used for formatting",
                                           *cur));
            }
            (_, &Known(ref ty)) => {
                self.ecx.span_err(sp,
                                  format!("argument previously used as a format \
                                           argument attempted to be used as `{}`",
                                           *ty));
            }
            (_, _) => {
                self.ecx.span_err(sp, "argument declared with multiple formats");
            }
        }
    }

    /// These attributes are applied to all statics that this syntax extension
    /// will generate.
    fn static_attrs(&self) -> Vec<ast::Attribute> {
        // Flag statics as `address_insignificant` so LLVM can merge duplicate
        // globals as much as possible (which we're generating a whole lot of).
        let unnamed = self.ecx
                          .meta_word(self.fmtsp,
                                     InternedString::new(
                                         "address_insignificant"));
        let unnamed = self.ecx.attribute(self.fmtsp, unnamed);

        // Do not warn format string as dead code
        let dead_code = self.ecx.meta_word(self.fmtsp,
                                           InternedString::new("dead_code"));
        let allow_dead_code = self.ecx.meta_list(self.fmtsp,
                                                 InternedString::new("allow"),
                                                 vec!(dead_code));
        let allow_dead_code = self.ecx.attribute(self.fmtsp, allow_dead_code);
        vec!(unnamed, allow_dead_code)
    }

    fn rtpath(&self, s: &str) -> Vec<ast::Ident> {
        vec!(self.ecx.ident_of("std"), self.ecx.ident_of("fmt"),
          self.ecx.ident_of("rt"), self.ecx.ident_of(s))
    }

    fn none(&self) -> P<ast::Expr> {
        let none = self.ecx.path_global(self.fmtsp, vec!(
                self.ecx.ident_of("std"),
                self.ecx.ident_of("option"),
                self.ecx.ident_of("None")));
        self.ecx.expr_path(none)
    }

    fn some(&self, e: P<ast::Expr>) -> P<ast::Expr> {
        let p = self.ecx.path_global(self.fmtsp, vec!(
                self.ecx.ident_of("std"),
                self.ecx.ident_of("option"),
                self.ecx.ident_of("Some")));
        let p = self.ecx.expr_path(p);
        self.ecx.expr_call(self.fmtsp, p, vec!(e))
    }

    fn trans_count(&self, c: parse::Count) -> P<ast::Expr> {
        let sp = self.fmtsp;
        match c {
            parse::CountIs(i) => {
                self.ecx.expr_call_global(sp, self.rtpath("CountIs"),
                                          vec!(self.ecx.expr_uint(sp, i)))
            }
            parse::CountIsParam(i) => {
                self.ecx.expr_call_global(sp, self.rtpath("CountIsParam"),
                                          vec!(self.ecx.expr_uint(sp, i)))
            }
            parse::CountImplied => {
                let path = self.ecx.path_global(sp, self.rtpath("CountImplied"));
                self.ecx.expr_path(path)
            }
            parse::CountIsNextParam => {
                let path = self.ecx.path_global(sp, self.rtpath("CountIsNextParam"));
                self.ecx.expr_path(path)
            }
            parse::CountIsName(n) => {
                let i = match self.name_positions.find_equiv(&n) {
                    Some(&i) => i,
                    None => 0, // error already emitted elsewhere
                };
                let i = i + self.args.len();
                self.ecx.expr_call_global(sp, self.rtpath("CountIsParam"),
                                          vec!(self.ecx.expr_uint(sp, i)))
            }
        }
    }

    fn trans_method(&mut self, method: &parse::Method) -> P<ast::Expr> {
        let sp = self.fmtsp;
        let method = match *method {
            parse::Select(ref arms, ref default) => {
                let arms = arms.iter().map(|arm| {
                        let p = self.ecx.path_global(sp, self.rtpath("SelectArm"));
                        let result = arm.result.iter().map(|p| {
                            self.trans_piece(p)
                        }).collect();
                        let s = token::intern_and_get_ident(arm.selector);
                        let selector = self.ecx.expr_str(sp, s);
                        self.ecx.expr_struct(sp, p, vec!(
                                self.ecx.field_imm(sp,
                                                   self.ecx.ident_of("selector"),
                                                   selector),
                                self.ecx.field_imm(sp, self.ecx.ident_of("result"),
                                                   self.ecx.expr_vec_slice(sp, result))))
                    }).collect();
                let default = default.iter().map(|p| {
                        self.trans_piece(p)
                    }).collect();
                self.ecx.expr_call_global(sp, self.rtpath("Select"), vec!(
                        self.ecx.expr_vec_slice(sp, arms),
                        self.ecx.expr_vec_slice(sp, default)))
            }
            parse::Plural(offset, ref arms, ref default) => {
                let offset = match offset {
                    Some(i) => { self.some(self.ecx.expr_uint(sp, i)) }
                    None => { self.none() }
                };
                let arms = arms.iter().map(|arm| {
                        let p = self.ecx.path_global(sp, self.rtpath("PluralArm"));
                        let result = arm.result.iter().map(|p| {
                                self.trans_piece(p)
                            }).collect();
                        let (lr, selarg) = match arm.selector {
                            parse::Keyword(t) => {
                                let p = self.rtpath(t.to_str());
                                let p = self.ecx.path_global(sp, p);
                                (self.rtpath("Keyword"), self.ecx.expr_path(p))
                            }
                            parse::Literal(i) => {
                                (self.rtpath("Literal"), self.ecx.expr_uint(sp, i))
                            }
                        };
                        let selector = self.ecx.expr_call_global(sp,
                                                                 lr, vec!(selarg));
                        self.ecx.expr_struct(sp, p, vec!(
                                self.ecx.field_imm(sp,
                                                   self.ecx.ident_of("selector"),
                                                   selector),
                                self.ecx.field_imm(sp, self.ecx.ident_of("result"),
                                                   self.ecx.expr_vec_slice(sp, result))))
                    }).collect();
                let default = default.iter().map(|p| {
                        self.trans_piece(p)
                    }).collect();
                self.ecx.expr_call_global(sp, self.rtpath("Plural"), vec!(
                        offset,
                        self.ecx.expr_vec_slice(sp, arms),
                        self.ecx.expr_vec_slice(sp, default)))
            }
        };
        let life = self.ecx.lifetime(sp, self.ecx.ident_of("static").name);
        let ty = self.ecx.ty_path(self.ecx.path_all(
                sp,
                true,
                self.rtpath("Method"),
                vec!(life),
                Vec::new()
                    ), None);
        let st = ast::ItemStatic(ty, ast::MutImmutable, method);
        let static_name = self.ecx.ident_of(format!("__STATIC_METHOD_{}",
                                                    self.method_statics.len()));
        let item = self.ecx.item(sp, static_name, self.static_attrs(), st);
        self.method_statics.push(item);
        self.ecx.expr_ident(sp, static_name)
    }

    /// Translate a `parse::Piece` to a static `rt::Piece`
    fn trans_piece(&mut self, piece: &parse::Piece) -> P<ast::Expr> {
        let sp = self.fmtsp;
        match *piece {
            parse::String(s) => {
                let s = token::intern_and_get_ident(s);
                self.ecx.expr_call_global(sp,
                                          self.rtpath("String"),
                                          vec!(
                    self.ecx.expr_str(sp, s)
                ))
            }
            parse::CurrentArgument => {
                let nil = self.ecx.expr_lit(sp, ast::LitNil);
                self.ecx.expr_call_global(sp, self.rtpath("CurrentArgument"), vec!(nil))
            }
            parse::Argument(ref arg) => {
                // Translate the position
                let pos = match arg.position {
                    // These two have a direct mapping
                    parse::ArgumentNext => {
                        let path = self.ecx.path_global(sp,
                                                        self.rtpath("ArgumentNext"));
                        self.ecx.expr_path(path)
                    }
                    parse::ArgumentIs(i) => {
                        self.ecx.expr_call_global(sp, self.rtpath("ArgumentIs"),
                                                  vec!(self.ecx.expr_uint(sp, i)))
                    }
                    // Named arguments are converted to positional arguments at
                    // the end of the list of arguments
                    parse::ArgumentNamed(n) => {
                        let i = match self.name_positions.find_equiv(&n) {
                            Some(&i) => i,
                            None => 0, // error already emitted elsewhere
                        };
                        let i = i + self.args.len();
                        self.ecx.expr_call_global(sp, self.rtpath("ArgumentIs"),
                                                  vec!(self.ecx.expr_uint(sp, i)))
                    }
                };

                // Translate the format
                let fill = match arg.format.fill { Some(c) => c, None => ' ' };
                let fill = self.ecx.expr_lit(sp, ast::LitChar(fill));
                let align = match arg.format.align {
                    parse::AlignLeft => {
                        self.ecx.path_global(sp, self.rtpath("AlignLeft"))
                    }
                    parse::AlignRight => {
                        self.ecx.path_global(sp, self.rtpath("AlignRight"))
                    }
                    parse::AlignUnknown => {
                        self.ecx.path_global(sp, self.rtpath("AlignUnknown"))
                    }
                };
                let align = self.ecx.expr_path(align);
                let flags = self.ecx.expr_uint(sp, arg.format.flags);
                let prec = self.trans_count(arg.format.precision);
                let width = self.trans_count(arg.format.width);
                let path = self.ecx.path_global(sp, self.rtpath("FormatSpec"));
                let fmt = self.ecx.expr_struct(sp, path, vec!(
                    self.ecx.field_imm(sp, self.ecx.ident_of("fill"), fill),
                    self.ecx.field_imm(sp, self.ecx.ident_of("align"), align),
                    self.ecx.field_imm(sp, self.ecx.ident_of("flags"), flags),
                    self.ecx.field_imm(sp, self.ecx.ident_of("precision"), prec),
                    self.ecx.field_imm(sp, self.ecx.ident_of("width"), width)));

                // Translate the method (if any)
                let method = match arg.method {
                    None => { self.none() }
                    Some(ref m) => {
                        let m = self.trans_method(*m);
                        self.some(self.ecx.expr_addr_of(sp, m))
                    }
                };
                let path = self.ecx.path_global(sp, self.rtpath("Argument"));
                let s = self.ecx.expr_struct(sp, path, vec!(
                    self.ecx.field_imm(sp, self.ecx.ident_of("position"), pos),
                    self.ecx.field_imm(sp, self.ecx.ident_of("format"), fmt),
                    self.ecx.field_imm(sp, self.ecx.ident_of("method"), method)));
                self.ecx.expr_call_global(sp, self.rtpath("Argument"), vec!(s))
            }
        }
    }

    /// Actually builds the expression which the iformat! block will be expanded
    /// to
    fn to_expr(self, invocation: Invocation) -> P<ast::Expr> {
        let static_attrs = self.static_attrs();
        // HACK(eddyb) working around #13703.
        let ecx = unsafe {&mut *(self.ecx as *mut _)};
        let Context {
            fmtsp,
            args,
            arg_types,
            names: cx_names,
            name_types,
            name_ordering,
            pieces,
            name_positions,
            method_statics,
            ..
        } = self;

        let mut lets = Vec::new();
        let mut locals = Vec::new();
        let mut names = Vec::from_fn(name_positions.len(), |_| None);
        let mut pats = Vec::new();
        let mut heads = Vec::new();

        // First, declare all of our methods that are statics
        for method in method_statics.move_iter() {
            let decl = respan(fmtsp, ast::DeclItem(method));
            lets.push(P(respan(fmtsp,
                               ast::StmtDecl(P(decl), ast::DUMMY_NODE_ID))));
        }

        // Next, build up the static array which will become our precompiled
        // format "string"
        let piece_ty = ecx.ty_path(ecx.path_all(
                fmtsp,
                true, vec!(
                    ecx.ident_of("std"),
                    ecx.ident_of("fmt"),
                    ecx.ident_of("rt"),
                    ecx.ident_of("Piece")),
                vec!(ecx.lifetime(fmtsp, ecx.ident_of("static").name)),
                Vec::new()
            ), None);
        let ty = ast::TyFixedLengthVec(
            piece_ty,
            ecx.expr_uint(fmtsp, pieces.len())
        );
        let ty = ecx.ty(fmtsp, ty);
        let fmt = ecx.expr_vec(fmtsp, pieces);
        let st = ast::ItemStatic(ty, ast::MutImmutable, fmt);
        let static_name = ecx.ident_of("__STATIC_FMTSTR");
        let item = ecx.item(fmtsp, static_name, static_attrs, st);
        let decl = respan(fmtsp, ast::DeclItem(item));
        lets.push(P(respan(fmtsp, ast::StmtDecl(P(decl), ast::DUMMY_NODE_ID))));

        // Right now there is a bug such that for the expression:
        //      foo(bar(&1))
        // the lifetime of `1` doesn't outlast the call to `bar`, so it's not
        // vald for the call to `foo`. To work around this all arguments to the
        // format! string are shoved into locals. Furthermore, we shove the address
        // of each variable because we don't want to move out of the arguments
        // passed to this function.
        for (i, e) in args.move_iter().enumerate() {
            let arg_ty = match *arg_types.get(i) {
                Some(ref ty) => ty,
                None => continue // error already generated
            };

            let name = ecx.ident_of(format!("__arg{}", i));
            pats.push(ecx.pat_ident(e.span, name));
            locals.push(format_arg(ecx, e.span, arg_ty,
                                   ecx.expr_ident(e.span, name)));
            heads.push(ecx.expr_addr_of(e.span, e));
        }
        for name in name_ordering.iter() {
            let e = match cx_names.find_copy(name) {
                Some(e) => {
                    if !name_types.contains_key(name) {
                        continue;
                    }
                    e
                }
                None => continue
            };

            let lname = ecx.ident_of(format!("__arg{}", *name));
            pats.push(ecx.pat_ident(e.span, lname));
            *names.get_mut(*name_positions.get(name)) =
                Some(format_arg(ecx, e.span,
                                name_types.get(name),
                                ecx.expr_ident(e.span, lname)));
            heads.push(ecx.expr_addr_of(e.span, e));
        }

        // Now create a vector containing all the arguments
        let slicename = ecx.ident_of("__args_vec");
        {
            let args = names.move_iter().map(|a| a.unwrap());
            let mut args = locals.move_iter().chain(args);
            let args = ecx.expr_vec_slice(fmtsp, args.collect());
            lets.push(ecx.stmt_let(fmtsp, false, slicename, args));
        }

        // Now create the fmt::Arguments struct with all our locals we created.
        let fmt = ecx.expr_ident(fmtsp, static_name);
        let args_slice = ecx.expr_ident(fmtsp, slicename);
        let result = ecx.expr_call_global(fmtsp, vec!(
                ecx.ident_of("std"),
                ecx.ident_of("fmt"),
                ecx.ident_of("Arguments"),
                ecx.ident_of("new")), vec!(fmt, args_slice));

        // We did all the work of making sure that the arguments
        // structure is safe, so we can safely have an unsafe block.
        let result = ecx.expr_block(P(ast::Block {
           view_items: Vec::new(),
           stmts: Vec::new(),
           expr: Some(result),
           id: ast::DUMMY_NODE_ID,
           rules: ast::UnsafeBlock(ast::CompilerGenerated),
           span: fmtsp,
        }));
        let resname = ecx.ident_of("__args");
        lets.push(ecx.stmt_let(fmtsp, false, resname, result));
        let res = ecx.expr_ident(fmtsp, resname);
        let result = match invocation {
            Call(e) => {
                let addr_of_extra = ecx.expr_addr_of(e.span, res);
                ecx.expr_call(e.span, e,
                              vec!(addr_of_extra))
            }
            MethodCall(e, m) => {
                let addr_of_extra = ecx.expr_addr_of(e.span, res);
                ecx.expr_method_call(e.span, e, m,
                                     vec!(addr_of_extra))
            }
        };
        let body = ecx.expr_block(ecx.block(fmtsp, lets, Some(result)));

        // Constructs an AST equivalent to:
        //
        //      match (&arg0, &arg1) {
        //          (tmp0, tmp1) => body
        //      }
        //
        // It was:
        //
        //      let tmp0 = &arg0;
        //      let tmp1 = &arg1;
        //      body
        //
        // Because of #11585 the new temporary lifetime rule, the enclosing
        // statements for these temporaries become the let's themselves.
        // If one or more of them are RefCell's, RefCell borrow() will also
        // end there; they don't last long enough for body to use them. The
        // match expression solves the scope problem.
        //
        // Note, it may also very well be transformed to:
        //
        //      match arg0 {
        //          ref tmp0 => {
        //              match arg1 => {
        //                  ref tmp1 => body } } }
        //
        // But the nested match expression is proved to perform not as well
        // as series of let's; the first approach does.
        let pat = ecx.pat(fmtsp, ast::PatTup(pats));
        let arm = ecx.arm(fmtsp, vec!(pat), body);
        let head = ecx.expr(fmtsp, ast::ExprTup(heads));
        ecx.expr_match(fmtsp, head, vec!(arm))
    }
}

fn format_arg(ecx: &ExtCtxt, sp: Span, arg_ty: &ArgumentType, arg: P<ast::Expr>)
                -> P<ast::Expr> {
    let fmt_fn = match *arg_ty {
        Known(ref tyname) => {
            match tyname.as_slice() {
                ""  => "secret_show",
                "?" => "secret_poly",
                "b" => "secret_bool",
                "c" => "secret_char",
                "d" | "i" => "secret_signed",
                "e" => "secret_lower_exp",
                "E" => "secret_upper_exp",
                "f" => "secret_float",
                "o" => "secret_octal",
                "p" => "secret_pointer",
                "s" => "secret_string",
                "t" => "secret_binary",
                "u" => "secret_unsigned",
                "x" => "secret_lower_hex",
                "X" => "secret_upper_hex",
                _ => {
                    ecx.span_err(sp, format!("unknown format trait `{}`",
                                                *tyname));
                    "dummy"
                }
            }
        }
        String => {
            return ecx.expr_call_global(sp, vec!(
                    ecx.ident_of("std"),
                    ecx.ident_of("fmt"),
                    ecx.ident_of("argumentstr")), vec!(arg))
        }
        Unsigned => {
            return ecx.expr_call_global(sp, vec!(
                    ecx.ident_of("std"),
                    ecx.ident_of("fmt"),
                    ecx.ident_of("argumentuint")), vec!(arg))
        }
    };

    let format_fn = ecx.path_global(sp, vec!(
            ecx.ident_of("std"),
            ecx.ident_of("fmt"),
            ecx.ident_of(fmt_fn)));
    ecx.expr_call_global(sp, vec!(
            ecx.ident_of("std"),
            ecx.ident_of("fmt"),
            ecx.ident_of("argument")), vec!(ecx.expr_path(format_fn), arg))
}

pub fn expand_format_args(ecx: &mut ExtCtxt, sp: Span,
                          tts: &[ast::TokenTree]) -> Box<base::MacResult> {

    match parse_args(ecx, sp, false, tts) {
        (invocation, Some((efmt, args, order, names))) => {
            MacExpr::new(expand_preparsed_format_args(ecx, sp, invocation, efmt,
                                                      args, order, names))
        }
        (_, None) => MacExpr::new(ecx.expr_uint(sp, 2))
    }
}

pub fn expand_format_args_method(ecx: &mut ExtCtxt, sp: Span,
                                 tts: &[ast::TokenTree]) -> Box<base::MacResult> {

    match parse_args(ecx, sp, true, tts) {
        (invocation, Some((efmt, args, order, names))) => {
            MacExpr::new(expand_preparsed_format_args(ecx, sp, invocation, efmt,
                                                      args, order, names))
        }
        (_, None) => MacExpr::new(ecx.expr_uint(sp, 2))
    }
}

/// Take the various parts of `format_args!(extra, efmt, args...,
/// name=names...)` and construct the appropriate formatting
/// expression.
pub fn expand_preparsed_format_args(ecx: &mut ExtCtxt, sp: Span,
                                    invocation: Invocation,
                                    efmt: P<ast::Expr>, args: Vec<P<ast::Expr>>,
                                    name_ordering: Vec<StrBuf>,
                                    names: HashMap<StrBuf, P<ast::Expr>>) -> P<ast::Expr> {
    let arg_types = Vec::from_fn(args.len(), |_| None);
    let mut cx = Context {
        ecx: ecx,
        args: args,
        arg_types: arg_types,
        names: names,
        name_positions: HashMap::new(),
        name_types: HashMap::new(),
        name_ordering: name_ordering,
        nest_level: 0,
        next_arg: 0,
        pieces: Vec::new(),
        method_statics: Vec::new(),
        fmtsp: sp,
    };
    cx.fmtsp = efmt.span;
    let fmt = match expr_to_str(cx.ecx,
                                efmt,
                                "format argument must be a string literal.") {
        Some((fmt, _)) => fmt,
        None => return DummyResult::raw_expr(sp)
    };

    let mut parser = parse::Parser::new(fmt.get());
    loop {
        match parser.next() {
            Some(piece) => {
                if parser.errors.len() > 0 { break }
                cx.verify_piece(&piece);
                let piece = cx.trans_piece(&piece);
                cx.pieces.push(piece);
            }
            None => break
        }
    }
    match parser.errors.shift() {
        Some(error) => {
            cx.ecx.span_err(cx.fmtsp,
                            format_strbuf!("invalid format string: {}",
                                           error).as_slice());
            return DummyResult::raw_expr(sp);
        }
        None => {}
    }

    // Make sure that all arguments were used and all arguments have types.
    for (i, ty) in cx.arg_types.iter().enumerate() {
        if ty.is_none() {
            cx.ecx.span_err(cx.args.get(i).span, "argument never used");
        }
    }
    for (name, e) in cx.names.iter() {
        if !cx.name_types.contains_key(name) {
            cx.ecx.span_err(e.span, "named argument never used");
        }
    }

    cx.to_expr(invocation)
}
