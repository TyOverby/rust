// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast::*;
use ast;
use ast_util;
use codemap::{respan, Span, Spanned};
use parse::token;
use ptr::P;
use owned_slice::OwnedSlice;
use util::small_vector::SmallVector;

use std::rc::Rc;

trait MoveMap<T> {
    fn move_map(self, f: |T| -> T) -> Self;
}

impl<T> MoveMap<T> for Vec<T> {
    fn move_map(mut self, f: |T| -> T) -> Vec<T> {
        use std::{mem, ptr};
        for p in self.mut_iter() {
            unsafe {
                // FIXME(#5016) this shouldn't need to zero to be safe.
                mem::move_val_init(p, f(ptr::read_and_zero(p)));
            }
        }
        self
    }
}

impl<T> MoveMap<T> for OwnedSlice<T> {
    fn move_map(self, f: |T| -> T) -> OwnedSlice<T> {
        OwnedSlice::from_vec(self.into_vec().move_map(f))
    }
}

// We may eventually want to be able to fold over type parameters, too.
pub trait Folder {
    fn fold_crate(&mut self, c: Crate) -> Crate {
        noop_fold_crate(c, self)
    }

    fn fold_meta_items(&mut self, meta_items: Vec<P<MetaItem>>) -> Vec<P<MetaItem>> {
        meta_items.move_map(|x| fold_meta_item_(x, self))
    }

    fn fold_view_path(&mut self, view_path: P<ViewPath>) -> P<ViewPath> {
        view_path.map(|Spanned {node, span}| {
            let inner_view_path = match node {
                ViewPathSimple(ident, path, node_id) => {
                    ViewPathSimple(ident, self.fold_path(path), self.new_id(node_id))
                }
                ViewPathGlob(path, node_id) => {
                    ViewPathGlob(self.fold_path(path), self.new_id(node_id))
                }
                ViewPathList(path, path_list_idents, node_id) => {
                    ViewPathList(self.fold_path(path),
                                 path_list_idents.move_map(|path_list_ident| {
                                    Spanned {
                                        node: PathListIdent_ {
                                            id: self.new_id(path_list_ident.node.id),
                                            name: path_list_ident.node.name,
                                        },
                                        span: self.new_span(path_list_ident.span)
                                    }
                                 }),
                                 self.new_id(node_id))
                }
            };
            Spanned {
                node: inner_view_path,
                span: self.new_span(span),
            }
        })
    }

    fn fold_view_item(&mut self, vi: ViewItem) -> ViewItem {
        noop_fold_view_item(vi, self)
    }

    fn fold_foreign_item(&mut self, ni: P<ForeignItem>) -> P<ForeignItem> {
        noop_fold_foreign_item(ni, self)
    }

    fn fold_item(&mut self, i: P<Item>) -> SmallVector<P<Item>> {
        noop_fold_item(i, self)
    }

    fn fold_struct_field(&mut self, sf: StructField) -> StructField {
        fold_struct_field(sf, self)
    }

    fn fold_item_underscore(&mut self, i: Item_) -> Item_ {
        noop_fold_item_underscore(i, self)
    }

    fn fold_fn_decl(&mut self, d: P<FnDecl>) -> P<FnDecl> {
        noop_fold_fn_decl(d, self)
    }

    fn fold_type_method(&mut self, m: TypeMethod) -> TypeMethod {
        noop_fold_type_method(m, self)
    }

    fn fold_method(&mut self, m: P<Method>) -> P<Method> {
        noop_fold_method(m, self)
    }

    fn fold_block(&mut self, b: P<Block>) -> P<Block> {
        noop_fold_block(b, self)
    }

    fn fold_stmt(&mut self, s: P<Stmt>) -> SmallVector<P<Stmt>> {
        s.and_then(|s| noop_fold_stmt(s, self))
    }

    fn fold_arm(&mut self, arm: Arm) -> Arm {
        // FIXME(eddyb) #14267 destructure in the argument.
        let Arm {attrs, pats, guard, body} = arm;
        Arm {
            attrs: attrs.move_map(|x| fold_attribute_(x, self)),
            pats: pats.move_map(|x| self.fold_pat(x)),
            guard: guard.map(|x| self.fold_expr(x)),
            body: self.fold_expr(body),
        }
    }

    fn fold_pat(&mut self, p: P<Pat>) -> P<Pat> {
        noop_fold_pat(p, self)
    }

    fn fold_decl(&mut self, d: P<Decl>) -> SmallVector<P<Decl>> {
        d.and_then(|Spanned {node, span}| match node {
            DeclLocal(l) => {
                SmallVector::one(P(Spanned {
                    node: DeclLocal(self.fold_local(l)),
                    span: self.new_span(span),
                }))
            }
            DeclItem(it) => {
                self.fold_item(it).move_iter().map(|i| {
                    P(Spanned {
                        node: DeclItem(i),
                        span: self.new_span(span),
                    })
                }).collect()
            }
        })
    }

    fn fold_expr(&mut self, e: P<Expr>) -> P<Expr> {
        e.map(|e| noop_fold_expr(e, self))
    }

    fn fold_ty(&mut self, t: P<Ty>) -> P<Ty> {
        t.map(|Ty {id, node, span}| {
            let node = match node {
                TyNil | TyBot | TyInfer => node.clone(),
                TyBox(ty) => TyBox(self.fold_ty(ty)),
                TyUniq(ty) => TyUniq(self.fold_ty(ty)),
                TyVec(ty) => TyVec(self.fold_ty(ty)),
                TyPtr(mt) => TyPtr(fold_mt(mt, self)),
                TyRptr(region, mt) => {
                    TyRptr(fold_opt_lifetime(region, self), fold_mt(mt, self))
                }
                TyClosure(f, region) => {
                    TyClosure(f.map(|ClosureTy {fn_style, onceness, bounds,
                                                decl, lifetimes}| ClosureTy {
                        fn_style: fn_style,
                        onceness: onceness,
                        bounds: fold_opt_bounds(bounds, self),
                        decl: self.fold_fn_decl(decl),
                        lifetimes: fold_lifetimes(lifetimes, self),
                    }), fold_opt_lifetime(region, self))
                }
                TyProc(f) => {
                    TyProc(f.map(|ClosureTy {fn_style, onceness, bounds,
                                             decl, lifetimes}| ClosureTy {
                        fn_style: fn_style,
                        onceness: onceness,
                        bounds: fold_opt_bounds(bounds, self),
                        decl: self.fold_fn_decl(decl),
                        lifetimes: fold_lifetimes(lifetimes, self),
                    }))
                }
                TyBareFn(f) => {
                    TyBareFn(f.map(|BareFnTy {lifetimes, fn_style, abi, decl}| BareFnTy {
                        lifetimes: fold_lifetimes(lifetimes, self),
                        fn_style: fn_style,
                        abi: abi,
                        decl: self.fold_fn_decl(decl)
                    }))
                }
                TyTup(tys) => TyTup(tys.move_map(|ty| self.fold_ty(ty))),
                TyPath(path, bounds, id) => {
                    TyPath(self.fold_path(path),
                        fold_opt_bounds(bounds, self),
                        self.new_id(id))
                }
                TyFixedLengthVec(ty, e) => {
                    TyFixedLengthVec(self.fold_ty(ty), self.fold_expr(e))
                }
                TyTypeof(expr) => TyTypeof(self.fold_expr(expr)),
            };
            Ty {
                id: self.new_id(id),
                node: node,
                span: self.new_span(span),
            }
        })
    }

    fn fold_mod(&mut self, m: Mod) -> Mod {
        noop_fold_mod(m, self)
    }

    fn fold_foreign_mod(&mut self, fm: ForeignMod) -> ForeignMod {
        // FIXME(eddyb) #14267 destructure in the argument.
        let ForeignMod {abi, view_items, items} = fm;
        ForeignMod {
            abi: abi,
            view_items: view_items.move_map(|x| self.fold_view_item(x)),
            items: items.move_map(|x| self.fold_foreign_item(x)),
        }
    }

    fn fold_variant(&mut self, v: P<Variant>) -> P<Variant> {
        v.map(|Spanned {node: Variant_ {id, name, attrs, kind, disr_expr, vis}, span}| {
            let kind = match kind {
                TupleVariantKind(variant_args) => {
                    TupleVariantKind(variant_args.move_map(|x| fold_variant_arg_(x, self)))
                }
                StructVariantKind(struct_def) => {
                    StructVariantKind(fold_struct_def(struct_def, self))
                }
            };

            Spanned {
                node: Variant_ {
                    id: self.new_id(id),
                    name: name,
                    attrs: attrs.move_map(|x| fold_attribute_(x, self)),
                    kind: kind,
                    disr_expr: disr_expr.map(|e| self.fold_expr(e)),
                    vis: vis,
                },
                span: self.new_span(span),
            }
        })
    }

    fn fold_ident(&mut self, i: Ident) -> Ident {
        i
    }

    fn fold_path(&mut self, path: Path) -> Path {
        // FIXME(eddyb) #14267 destructure in the argument.
        let Path {global, segments, span} = path;
        Path {
            global: global,
            segments: segments.move_map(|PathSegment {identifier, lifetimes, types}| PathSegment {
                identifier: self.fold_ident(identifier),
                lifetimes: fold_lifetimes(lifetimes, self),
                types: types.move_map(|typ| self.fold_ty(typ)),
            }),
            span: self.new_span(span)
        }
    }

    fn fold_local(&mut self, l: P<Local>) -> P<Local> {
        l.map(|Local {id, ty, pat, init, span}| Local {
            id: self.new_id(id), // Needs to be first, for ast_map.
            ty: self.fold_ty(ty),
            pat: self.fold_pat(pat),
            init: init.map(|e| self.fold_expr(e)),
            span: self.new_span(span),
        })
    }

    fn fold_mac(&mut self, mac: Mac) -> Mac {
        // FIXME(eddyb) #14267 destructure in the argument.
        let Spanned {node, span} = mac;
        Spanned {
            node: match node {
                MacInvocTT(p, tts, ctxt) => {
                    MacInvocTT(self.fold_path(p), fold_tts(tts.as_slice(), self), ctxt)
                }
            },
            span: self.new_span(span)
        }
    }

    fn map_exprs(&self, f: |P<Expr>| -> P<Expr>, es: Vec<P<Expr>>) -> Vec<P<Expr>> {
        es.move_map(|x| f(x))
    }

    fn new_id(&mut self, i: NodeId) -> NodeId {
        i
    }

    fn new_span(&mut self, sp: Span) -> Span {
        sp
    }

    fn fold_explicit_self(&mut self, es: ExplicitSelf) -> ExplicitSelf {
        // FIXME(eddyb) #14267 destructure in the argument.
        let Spanned {node, span} = es;
        Spanned {
            node: self.fold_explicit_self_(node),
            span: self.new_span(span)
        }
    }

    fn fold_explicit_self_(&mut self, es: ExplicitSelf_) -> ExplicitSelf_ {
        match es {
            SelfStatic | SelfValue | SelfUniq => es,
            SelfRegion(lifetime, m) => {
                SelfRegion(fold_opt_lifetime(lifetime, self), m)
            }
        }
    }

    fn fold_lifetime(&mut self, l: Lifetime) -> Lifetime {
        noop_fold_lifetime(l, self)
    }
}

/* some little folds that probably aren't useful to have in Folder itself*/

//used in noop_fold_item and noop_fold_crate and noop_fold_crate_directive
fn fold_meta_item_<T: Folder>(mi: P<MetaItem>, fld: &mut T) -> P<MetaItem> {
    mi.map(|Spanned {node, span}| Spanned {
        node: match node {
            MetaWord(id) => MetaWord(id),
            MetaList(id, mis) => {
                MetaList(id, mis.move_map(|e| fold_meta_item_(e, fld)))
            }
            MetaNameValue(id, s) => MetaNameValue(id, s)
        },
        span: fld.new_span(span)
    })
}

//used in noop_fold_item and noop_fold_crate
fn fold_attribute_<T: Folder>(Spanned {node, span}: Attribute, fld: &mut T) -> Attribute {
    Spanned {
        span: fld.new_span(span),
        node: ast::Attribute_ {
            style: node.style,
            is_sugared_doc: node.is_sugared_doc,
            value: fold_meta_item_(node.value, fld)
        }
    }
}

//used in noop_fold_foreign_item and noop_fold_fn_decl
fn fold_arg_<T: Folder>(Arg {id, ty, pat}: Arg, fld: &mut T) -> Arg {
    Arg {
        id: fld.new_id(id), // Needs to be first, for ast_map.
        ty: fld.fold_ty(ty),
        pat: fld.fold_pat(pat),
    }
}

// build a new vector of tts by appling the Folder's fold_ident to
// all of the identifiers in the token trees.
//
// This is part of hygiene magic. As far as hygiene is concerned, there
// are three types of let pattern bindings or loop labels:
//      - those defined and used in non-macro part of the program
//      - those used as part of macro invocation arguments
//      - those defined and used inside macro definitions
// Lexically, type 1 and 2 are in one group and type 3 the other. If they
// clash, in order for let and loop label to work hygienically, one group
// or the other needs to be renamed. The problem is that type 2 and 3 are
// parsed together (inside the macro expand function). After being parsed and
// AST being constructed, they can no longer be distinguished from each other.
//
// For that reason, type 2 let bindings and loop labels are actually renamed
// in the form of tokens instead of AST nodes, here. There are wasted effort
// since many token::IDENT are not necessary part of let bindings and most
// token::LIFETIME are certainly not loop labels. But we can't tell in their
// token form. So this is less ideal and hacky but it works.
pub fn fold_tts<T: Folder>(tts: &[TokenTree], fld: &mut T) -> Vec<TokenTree> {
    tts.iter().map(|tt| match *tt {
        TTTok(span, ref tok) => TTTok(span, maybe_fold_ident(tok.clone(), fld)),
        TTDelim(ref tts) => TTDelim(Rc::new(fold_tts(tts.as_slice(), fld))),
        TTSeq(span, ref pattern, ref sep, is_optional) => {
            TTSeq(span, Rc::new(fold_tts(pattern.as_slice(), fld)),
                  sep.clone().map(|tok| maybe_fold_ident(tok, fld)),
                  is_optional)
        }
        TTNonterminal(sp, ident) => TTNonterminal(sp, fld.fold_ident(ident))
    }).collect()
}

// apply ident folder if it's an ident, otherwise leave it alone
fn maybe_fold_ident<T: Folder>(t: token::Token, fld: &mut T) -> token::Token {
    match t {
        token::IDENT(id, followed_by_colons) => {
            token::IDENT(fld.fold_ident(id), followed_by_colons)
        }
        token::LIFETIME(id) => token::LIFETIME(fld.fold_ident(id)),
        _ => t
    }
}

pub fn noop_fold_fn_decl<T: Folder>(decl: P<FnDecl>, fld: &mut T) -> P<FnDecl> {
    decl.map(|FnDecl {inputs, output, cf, variadic}| FnDecl {
        inputs: inputs.move_map(|x| fold_arg_(x, fld)),
        output: fld.fold_ty(output),
        cf: cf,
        variadic: variadic
    })
}

fn fold_ty_param_bound<T: Folder>(tpb: TyParamBound, fld: &mut T) -> TyParamBound {
    match tpb {
        TraitTyParamBound(ty) => TraitTyParamBound(fold_trait_ref(ty, fld)),
        StaticRegionTyParamBound => StaticRegionTyParamBound,
        OtherRegionTyParamBound(s) => OtherRegionTyParamBound(s)
    }
}

pub fn fold_ty_param<T: Folder>(TyParam {id, ident, sized, bounds, default, span}: TyParam,
                                fld: &mut T) -> TyParam {
    TyParam {
        id: fld.new_id(id),
        ident: ident,
        sized: sized,
        bounds: bounds.move_map(|x| fold_ty_param_bound(x, fld)),
        default: default.map(|x| fld.fold_ty(x)),
        span: fld.new_span(span)
    }
}

pub fn fold_ty_params<T: Folder>(tps: OwnedSlice<TyParam>, fld: &mut T)
                                   -> OwnedSlice<TyParam> {
    tps.move_map(|tp| fold_ty_param(tp, fld))
}

pub fn noop_fold_lifetime<T: Folder>(l: Lifetime, fld: &mut T) -> Lifetime {
    Lifetime {
        id: fld.new_id(l.id),
        name: l.name,
        span: fld.new_span(l.span)
    }
}

pub fn fold_lifetimes<T: Folder>(lts: Vec<Lifetime>, fld: &mut T) -> Vec<Lifetime> {
    lts.move_map(|l| fld.fold_lifetime(l))
}

pub fn fold_opt_lifetime<T: Folder>(o_lt: Option<Lifetime>, fld: &mut T) -> Option<Lifetime> {
    o_lt.map(|lt| fld.fold_lifetime(lt))
}

pub fn fold_generics<T: Folder>(Generics {ty_params, lifetimes}: Generics,
                                fld: &mut T) -> Generics {
    Generics {
        ty_params: fold_ty_params(ty_params, fld),
        lifetimes: fold_lifetimes(lifetimes, fld)
    }
}

fn fold_struct_def<T: Folder>(struct_def: P<StructDef>, fld: &mut T) -> P<StructDef> {
    struct_def.map(|StructDef {fields, ctor_id, super_struct, is_virtual}| StructDef {
        fields: fields.move_map(|f| fld.fold_struct_field(f)),
        ctor_id: ctor_id.map(|cid| fld.new_id(cid)),
        super_struct: super_struct.map(|t| fld.fold_ty(t)),
        is_virtual: is_virtual
    })
}

fn fold_trait_ref<T: Folder>(TraitRef {ref_id, path}: TraitRef, fld: &mut T) -> TraitRef {
    TraitRef {
        ref_id: fld.new_id(ref_id),
        path: fld.fold_path(path),
    }
}

fn fold_struct_field<T: Folder>(Spanned {node, span}: StructField, fld: &mut T) -> StructField {
    let StructField_ {id, kind, ty, attrs} = node;
    Spanned {
        node: StructField_ {
            id: fld.new_id(id),
            kind: kind,
            ty: fld.fold_ty(ty),
            attrs: attrs.move_map(|e| fold_attribute_(e, fld))
        },
        span: fld.new_span(span)
    }
}

fn fold_field_<T: Folder>(Field {ident, expr, span}: Field, folder: &mut T) -> Field {
    ast::Field {
        ident: respan(ident.span, folder.fold_ident(ident.node)),
        expr: folder.fold_expr(expr),
        span: folder.new_span(span),
    }
}

fn fold_mt<T: Folder>(MutTy {ty, mutbl}: MutTy, folder: &mut T) -> MutTy {
    MutTy {
        ty: folder.fold_ty(ty),
        mutbl: mutbl,
    }
}

fn fold_opt_bounds<T: Folder>(b: Option<OwnedSlice<TyParamBound>>, folder: &mut T)
                              -> Option<OwnedSlice<TyParamBound>> {
    b.map(|bounds| bounds.move_map(|bound| {
        fold_ty_param_bound(bound, folder)
    }))
}

fn fold_variant_arg_<T: Folder>(VariantArg {ty, id}: VariantArg, folder: &mut T)
                                -> VariantArg {
    VariantArg {
        id: folder.new_id(id),
        ty: folder.fold_ty(ty)
    }
}

pub fn noop_fold_view_item<T: Folder>(ViewItem {node, attrs, vis, span}: ViewItem,
                                      folder: &mut T) -> ViewItem {
    ViewItem {
        node: match node {
            ViewItemExternCrate(ident, string, node_id) => {
                ViewItemExternCrate(ident, string,
                                    folder.new_id(node_id))
            }
            ViewItemUse(view_path) => {
                ViewItemUse(folder.fold_view_path(view_path))
            }
        },
        attrs: attrs.move_map(|a| fold_attribute_(a, folder)),
        vis: vis,
        span: folder.new_span(span),
    }
}

pub fn noop_fold_block<T: Folder>(b: P<Block>, folder: &mut T) -> P<Block> {
    b.map(|Block {id, view_items, stmts, expr, rules, span}| Block {
        id: folder.new_id(id), // Needs to be first, for ast_map.
        view_items: view_items.move_map(|x| folder.fold_view_item(x)),
        stmts: stmts.move_iter().flat_map(|s| folder.fold_stmt(s).move_iter()).collect(),
        expr: expr.map(|x| folder.fold_expr(x)),
        rules: rules,
        span: folder.new_span(span),
    })
}

pub fn noop_fold_item_underscore<T: Folder>(i: Item_, folder: &mut T) -> Item_ {
    match i {
        ItemStatic(t, m, e) => {
            ItemStatic(folder.fold_ty(t), m, folder.fold_expr(e))
        }
        ItemFn(decl, fn_style, abi, generics, body) => {
            ItemFn(
                folder.fold_fn_decl(decl),
                fn_style,
                abi,
                fold_generics(generics, folder),
                folder.fold_block(body)
            )
        }
        ItemMod(m) => ItemMod(folder.fold_mod(m)),
        ItemForeignMod(nm) => ItemForeignMod(folder.fold_foreign_mod(nm)),
        ItemTy(t, generics) => {
            ItemTy(folder.fold_ty(t), fold_generics(generics, folder))
        }
        ItemEnum(enum_definition, generics) => {
            ItemEnum(
                ast::EnumDef {
                    variants: enum_definition.variants.move_map(|x| folder.fold_variant(x)),
                },
                fold_generics(generics, folder))
        }
        ItemStruct(struct_def, generics) => {
            let struct_def = fold_struct_def(struct_def, folder);
            ItemStruct(struct_def, fold_generics(generics, folder))
        }
        ItemImpl(generics, ifce, ty, methods) => {
            ItemImpl(fold_generics(generics, folder),
                     ifce.map(|p| fold_trait_ref(p, folder)),
                     folder.fold_ty(ty),
                     methods.move_map(|x| folder.fold_method(x))
            )
        }
        ItemTrait(generics, sized, traits, methods) => {
            let methods = methods.move_map(|method| {
                match method {
                    Required(m) => Required(folder.fold_type_method(m)),
                    Provided(method) => Provided(folder.fold_method(method))
                }
            });
            ItemTrait(fold_generics(generics, folder),
                      sized,
                      traits.move_map(|p| fold_trait_ref(p, folder)),
                      methods)
        }
        ItemMac(m) => ItemMac(folder.fold_mac(m)),
    }
}

pub fn noop_fold_type_method<T: Folder>(m: TypeMethod, fld: &mut T) -> TypeMethod {
    let TypeMethod {id, ident, attrs, fn_style, decl, generics, explicit_self, span} = m;
    TypeMethod {
        id: fld.new_id(id), // Needs to be first, for ast_map.
        ident: fld.fold_ident(ident),
        attrs: attrs.move_map(|a| fold_attribute_(a, fld)),
        fn_style: fn_style,
        decl: fld.fold_fn_decl(decl),
        generics: fold_generics(generics, fld),
        explicit_self: fld.fold_explicit_self(explicit_self),
        span: fld.new_span(span),
    }
}

pub fn noop_fold_mod<T: Folder>(Mod {inner, view_items, items}: Mod, folder: &mut T) -> Mod {
    Mod {
        inner: folder.new_span(inner),
        view_items: view_items.move_map(|x| folder.fold_view_item(x)),
        items: items.move_iter().flat_map(|x| folder.fold_item(x).move_iter()).collect(),
    }
}

pub fn noop_fold_crate<T: Folder>(Crate {module, attrs, config, span}: Crate,
                                  folder: &mut T) -> Crate {
    Crate {
        attrs: attrs.move_map(|x| fold_attribute_(x, folder)),
        config: config.move_map(|x| fold_meta_item_(x, folder)),
        module: folder.fold_mod(module),
        span: folder.new_span(span),
    }
}

pub fn noop_fold_item<T: Folder>(i: P<Item>, folder: &mut T) -> SmallVector<P<Item>> {
    i.and_then(|Item {id, ident, attrs, node, vis, span}| {
        let id = folder.new_id(id); // Needs to be first, for ast_map.
        let node = folder.fold_item_underscore(node);
        let ident = match node {
            // The node may have changed, recompute the "pretty" impl name.
            ItemImpl(_, ref maybe_trait, ref ty, _) => {
                ast_util::impl_pretty_name(maybe_trait, &**ty)
            }
            _ => ident
        };

        SmallVector::one(P(Item {
            id: id,
            ident: folder.fold_ident(ident),
            attrs: attrs.move_map(|e| fold_attribute_(e, folder)),
            node: node,
            vis: vis,
            span: folder.new_span(span)
        }))
    })
}

pub fn noop_fold_foreign_item<T: Folder>(ni: P<ForeignItem>, folder: &mut T) -> P<ForeignItem> {
    ni.map(|ForeignItem {id, ident, attrs, node, span, vis}| ForeignItem {
        id: folder.new_id(id), // Needs to be first, for ast_map.
        ident: folder.fold_ident(ident),
        attrs: attrs.move_map(|x| fold_attribute_(x, folder)),
        node: match node {
            ForeignItemFn(fdec, generics) => {
                ForeignItemFn(fdec.map(|FnDecl {inputs, output, cf, variadic}| FnDecl {
                    inputs: inputs.move_map(|a| fold_arg_(a, folder)),
                    output: folder.fold_ty(output),
                    cf: cf,
                    variadic: variadic
                }), fold_generics(generics, folder))
            }
            ForeignItemStatic(t, m) => {
                ForeignItemStatic(folder.fold_ty(t), m)
            }
        },
        span: folder.new_span(span),
        vis: vis,
    })
}

pub fn noop_fold_method<T: Folder>(m: P<Method>, folder: &mut T) -> P<Method> {
    m.map(|Method {id, ident, attrs, generics, explicit_self, fn_style, decl, body, span, vis}| {
        Method {
            id: folder.new_id(id), // Needs to be first, for ast_map.
            ident: folder.fold_ident(ident),
            attrs: attrs.move_map(|a| fold_attribute_(a, folder)),
            generics: fold_generics(generics, folder),
            explicit_self: folder.fold_explicit_self(explicit_self),
            fn_style: fn_style,
            decl: folder.fold_fn_decl(decl),
            body: folder.fold_block(body),
            span: folder.new_span(span),
            vis: vis
        }
    })
}

pub fn noop_fold_pat<T: Folder>(p: P<Pat>, folder: &mut T) -> P<Pat> {
    p.map(|Pat {id, node, span}| Pat {
        id: folder.new_id(id),
        node: match node {
            PatWild => PatWild,
            PatWildMulti => PatWildMulti,
            PatIdent(binding_mode, pth, sub) => {
                PatIdent(binding_mode,
                         folder.fold_path(pth),
                         sub.map(|x| folder.fold_pat(x)))
            }
            PatLit(e) => PatLit(folder.fold_expr(e)),
            PatEnum(pth, pats) => {
                PatEnum(folder.fold_path(pth),
                        pats.map(|pats| pats.move_map(|x| folder.fold_pat(x))))
            }
            PatStruct(pth, fields, etc) => {
                let pth_ = folder.fold_path(pth);
                let fs = fields.move_map(|FieldPat {ident, pat}| FieldPat {
                    ident: ident,
                    pat: folder.fold_pat(pat)
                });
                PatStruct(pth_, fs, etc)
            }
            PatTup(elts) => PatTup(elts.move_map(|x| folder.fold_pat(x))),
            PatUniq(inner) => PatUniq(folder.fold_pat(inner)),
            PatRegion(inner) => PatRegion(folder.fold_pat(inner)),
            PatRange(e1, e2) => {
                PatRange(folder.fold_expr(e1), folder.fold_expr(e2))
            },
            PatVec(before, slice, after) => {
                PatVec(before.move_map(|x| folder.fold_pat(x)),
                       slice.map(|x| folder.fold_pat(x)),
                       after.move_map(|x| folder.fold_pat(x)))
            }
        },
        span: folder.new_span(span),
    })
}

pub fn noop_fold_expr<T: Folder>(Expr {id, node, span}: Expr, folder: &mut T) -> Expr {
    Expr {
        id: folder.new_id(id),
        node: match node {
            ExprVstore(e, v) => {
                ExprVstore(folder.fold_expr(e), v)
            }
            ExprBox(p, e) => {
                ExprBox(folder.fold_expr(p), folder.fold_expr(e))
            }
            ExprVec(exprs) => {
                ExprVec(exprs.move_map(|x| folder.fold_expr(x)))
            }
            ExprRepeat(expr, count) => {
                ExprRepeat(folder.fold_expr(expr), folder.fold_expr(count))
            }
            ExprTup(elts) => ExprTup(elts.move_map(|x| folder.fold_expr(x))),
            ExprCall(f, args) => {
                ExprCall(folder.fold_expr(f),
                        args.move_map(|x| folder.fold_expr(x)))
            }
            ExprMethodCall(i, tps, args) => {
                ExprMethodCall(
                    respan(i.span, folder.fold_ident(i.node)),
                    tps.move_map(|x| folder.fold_ty(x)),
                    args.move_map(|x| folder.fold_expr(x)))
            }
            ExprBinary(binop, lhs, rhs) => {
                ExprBinary(binop,
                        folder.fold_expr(lhs),
                        folder.fold_expr(rhs))
            }
            ExprUnary(binop, ohs) => {
                ExprUnary(binop, folder.fold_expr(ohs))
            }
            ExprLit(_) => node.clone(),
            ExprCast(expr, ty) => {
                ExprCast(folder.fold_expr(expr), folder.fold_ty(ty))
            }
            ExprAddrOf(m, ohs) => ExprAddrOf(m, folder.fold_expr(ohs)),
            ExprIf(cond, tr, fl) => {
                ExprIf(folder.fold_expr(cond),
                    folder.fold_block(tr),
                    fl.map(|x| folder.fold_expr(x)))
            }
            ExprWhile(cond, body) => {
                ExprWhile(folder.fold_expr(cond), folder.fold_block(body))
            }
            ExprForLoop(pat, iter, body, maybe_ident) => {
                ExprForLoop(folder.fold_pat(pat),
                            folder.fold_expr(iter),
                            folder.fold_block(body),
                            maybe_ident.map(|i| folder.fold_ident(i)))
            }
            ExprLoop(body, opt_ident) => {
                ExprLoop(folder.fold_block(body),
                        opt_ident.map(|x| folder.fold_ident(x)))
            }
            ExprMatch(expr, arms) => {
                ExprMatch(folder.fold_expr(expr),
                        arms.move_map(|x| folder.fold_arm(x)))
            }
            ExprFnBlock(decl, body) => {
                ExprFnBlock(folder.fold_fn_decl(decl), folder.fold_block(body))
            }
            ExprProc(decl, body) => {
                ExprProc(folder.fold_fn_decl(decl), folder.fold_block(body))
            }
            ExprBlock(blk) => ExprBlock(folder.fold_block(blk)),
            ExprAssign(el, er) => {
                ExprAssign(folder.fold_expr(el), folder.fold_expr(er))
            }
            ExprAssignOp(op, el, er) => {
                ExprAssignOp(op,
                            folder.fold_expr(el),
                            folder.fold_expr(er))
            }
            ExprField(el, id, tys) => {
                ExprField(folder.fold_expr(el),
                          folder.fold_ident(id),
                          tys.move_map(|x| folder.fold_ty(x)))
            }
            ExprIndex(el, er) => {
                ExprIndex(folder.fold_expr(el), folder.fold_expr(er))
            }
            ExprPath(pth) => ExprPath(folder.fold_path(pth)),
            ExprBreak(opt_ident) => ExprBreak(opt_ident.map(|x| folder.fold_ident(x))),
            ExprAgain(opt_ident) => ExprAgain(opt_ident.map(|x| folder.fold_ident(x))),
            ExprRet(e) => {
                ExprRet(e.map(|x| folder.fold_expr(x)))
            }
            ExprInlineAsm(InlineAsm {
                inputs,
                outputs,
                asm,
                asm_str_style,
                clobbers,
                volatile,
                alignstack,
                dialect
            }) => ExprInlineAsm(InlineAsm {
                inputs: inputs.move_map(|(c, input)| {
                    (c, folder.fold_expr(input))
                }),
                outputs: outputs.move_map(|(c, out)| {
                    (c, folder.fold_expr(out))
                }),
                asm: asm,
                asm_str_style: asm_str_style,
                clobbers: clobbers,
                volatile: volatile,
                alignstack: alignstack,
                dialect: dialect
            }),
            ExprMac(mac) => ExprMac(folder.fold_mac(mac)),
            ExprStruct(path, fields, maybe_expr) => {
                ExprStruct(folder.fold_path(path),
                        fields.move_map(|x| fold_field_(x, folder)),
                        maybe_expr.map(|x| folder.fold_expr(x)))
            },
            ExprParen(ex) => ExprParen(folder.fold_expr(ex))
        },
        span: folder.new_span(span),
    }
}

pub fn noop_fold_stmt<T: Folder>(Spanned {node, span}: Stmt, folder: &mut T)
                                 -> SmallVector<P<Stmt>> {
    let span = folder.new_span(span);
    match node {
        StmtDecl(d, id) => {
            let id = folder.new_id(id);
            folder.fold_decl(d).move_iter().map(|d| P(Spanned {
                node: StmtDecl(d, id),
                span: span
            })).collect()
        }
        StmtExpr(e, id) => {
            let id = folder.new_id(id);
            SmallVector::one(P(Spanned {
                node: StmtExpr(folder.fold_expr(e), id),
                span: span
            }))
        }
        StmtSemi(e, id) => {
            let id = folder.new_id(id);
            SmallVector::one(P(Spanned {
                node: StmtSemi(folder.fold_expr(e), id),
                span: span
            }))
        }
        StmtMac(mac, semi) => SmallVector::one(P(Spanned {
            node: StmtMac(folder.fold_mac(mac), semi),
            span: span
        }))
    }
}

#[cfg(test)]
mod test {
    use std::io;
    use ast;
    use util::parser_testing::{string_to_crate, matches_codepattern};
    use parse::token;
    use print::pprust;
    use super::*;

    // this version doesn't care about getting comments or docstrings in.
    fn fake_print_crate(s: &mut pprust::State,
                        krate: &ast::Crate) -> io::IoResult<()> {
        s.print_mod(&krate.module, krate.attrs.as_slice())
    }

    // change every identifier to "zz"
    struct ToZzIdentFolder;

    impl Folder for ToZzIdentFolder {
        fn fold_ident(&mut self, _: ast::Ident) -> ast::Ident {
            token::str_to_ident("zz")
        }
    }

    // maybe add to expand.rs...
    macro_rules! assert_pred (
        ($pred:expr, $predname:expr, $a:expr , $b:expr) => (
            {
                let pred_val = $pred;
                let a_val = $a;
                let b_val = $b;
                if !(pred_val(a_val.as_slice(),b_val.as_slice())) {
                    fail!("expected args satisfying {}, got {:?} and {:?}",
                          $predname, a_val, b_val);
                }
            }
        )
    )

    // make sure idents get transformed everywhere
    #[test] fn ident_transformation () {
        let mut zz_fold = ToZzIdentFolder;
        let ast = string_to_crate(
            "#[a] mod b {fn c (d : e, f : g) {h!(i,j,k);l;m}}".to_strbuf());
        let folded_crate = zz_fold.fold_crate(ast);
        assert_pred!(
            matches_codepattern,
            "matches_codepattern",
            pprust::to_str(|s| fake_print_crate(s, &folded_crate)),
            "#[a]mod zz{fn zz(zz:zz,zz:zz){zz!(zz,zz,zz);zz;zz}}".to_strbuf());
    }

    // even inside macro defs....
    #[test] fn ident_transformation_in_defs () {
        let mut zz_fold = ToZzIdentFolder;
        let ast = string_to_crate(
            "macro_rules! a {(b $c:expr $(d $e:token)f+ => \
             (g $(d $d $e)+))} ".to_strbuf());
        let folded_crate = zz_fold.fold_crate(ast);
        assert_pred!(
            matches_codepattern,
            "matches_codepattern",
            pprust::to_str(|s| fake_print_crate(s, &folded_crate)),
            "zz!zz((zz$zz:zz$(zz $zz:zz)zz+=>(zz$(zz$zz$zz)+)))".to_strbuf());
    }
}
