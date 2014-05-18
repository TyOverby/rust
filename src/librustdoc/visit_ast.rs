// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Rust AST Visitor. Extracts useful information and massages it into a form
//! usable for clean

use syntax::abi;
use syntax::ast;
use syntax::ast_util;
use syntax::ast_map;
use syntax::attr::AttrMetaMethods;
use syntax::codemap::Span;
use syntax::ptr::P;

use core;
use doctree::*;

pub struct RustdocVisitor<'a> {
    pub module: Module,
    pub attrs: Vec<ast::Attribute>,
    pub cx: &'a core::DocContext,
    pub analysis: Option<&'a core::CrateAnalysis>,
}

impl<'a> RustdocVisitor<'a> {
    pub fn new<'b>(cx: &'b core::DocContext,
                   analysis: Option<&'b core::CrateAnalysis>) -> RustdocVisitor<'b> {
        RustdocVisitor {
            module: Module::new(None),
            attrs: Vec::new(),
            cx: cx,
            analysis: analysis,
        }
    }

    pub fn visit(&mut self, krate: &ast::Crate) {
        self.attrs = krate.attrs.clone();

        self.module = self.visit_mod_contents(krate.span,
                                              krate.attrs.clone(),
                                              ast::Public,
                                              ast::CRATE_NODE_ID,
                                              &krate.module,
                                              None);
        self.module.is_crate = true;
    }

    pub fn visit_struct_def(&mut self, item: &ast::Item, sd: &ast::StructDef,
                            generics: &ast::Generics) -> Struct {
        debug!("Visiting struct");
        let struct_type = struct_type_from_def(sd);
        Struct {
            id: item.id,
            struct_type: struct_type,
            name: item.ident,
            vis: item.vis,
            attrs: item.attrs.clone(),
            generics: generics.clone(),
            fields: sd.fields.clone(),
            where: item.span
        }
    }

    pub fn visit_enum_def(&mut self, it: &ast::Item, def: &ast::EnumDef,
                          params: &ast::Generics) -> Enum {
        debug!("Visiting enum");
        Enum {
            name: it.ident,
            variants: def.variants.iter().map(|v| Variant {
                name: v.node.name,
                attrs: v.node.attrs.clone(),
                vis: v.node.vis,
                id: v.node.id,
                kind: v.node.kind.clone(),
                where: v.span,
            }).collect(),
            vis: it.vis,
            generics: params.clone(),
            attrs: it.attrs.clone(),
            id: it.id,
            where: it.span,
        }
    }

    pub fn visit_fn(&mut self, item: &ast::Item, fd: &ast::FnDecl,
                    fn_style: &ast::FnStyle, _abi: &abi::Abi,
                    gen: &ast::Generics) -> Function {
        debug!("Visiting fn");
        Function {
            id: item.id,
            vis: item.vis,
            attrs: item.attrs.clone(),
            decl: fd.clone(),
            name: item.ident,
            where: item.span,
            generics: gen.clone(),
            fn_style: *fn_style,
        }
    }

    pub fn visit_mod_contents(&mut self, span: Span, attrs: Vec<ast::Attribute> ,
                              vis: ast::Visibility, id: ast::NodeId,
                              m: &ast::Mod,
                              name: Option<ast::Ident>) -> Module {
        let mut om = Module::new(name);
        for item in m.view_items.iter() {
            self.visit_view_item(item, &mut om);
        }
        om.where_outer = span;
        om.where_inner = m.inner;
        om.attrs = attrs;
        om.vis = vis;
        om.id = id;
        for i in m.items.iter() {
            self.visit_item(&**i, &mut om);
        }
        om
    }

    pub fn visit_view_item(&mut self, item: &ast::ViewItem, om: &mut Module) {
        if item.vis != ast::Public {
            return om.view_items.push(item.clone());
        }
        let please_inline = item.attrs.iter().any(|item| {
            match item.meta_item_list() {
                Some(list) => {
                    list.iter().any(|i| i.name().get() == "inline")
                }
                None => false,
            }
        });
        let item = match item.node {
            ast::ViewItemUse(ref vpath) => {
                match self.visit_view_path(&**vpath, om, please_inline) {
                    None => return,
                    Some(path) => {
                        ast::ViewItem {
                            node: ast::ViewItemUse(path),
                            .. item.clone()
                        }
                    }
                }
            }
            ast::ViewItemExternCrate(..) => item.clone()
        };
        om.view_items.push(item);
    }

    fn visit_view_path(&mut self, path: &ast::ViewPath,
                       om: &mut Module,
                       please_inline: bool) -> Option<P<ast::ViewPath>> {
        match path.node {
            ast::ViewPathSimple(_, _, id) => {
                if self.resolve_id(id, false, om, please_inline) { return None }
            }
            ast::ViewPathList(ref p, ref paths, ref b) => {
                let mut mine = Vec::new();
                for path in paths.iter() {
                    if !self.resolve_id(path.node.id, false, om, please_inline) {
                        mine.push(path.clone());
                    }
                }

                if mine.len() == 0 { return None }
                return Some(P(::syntax::codemap::Spanned {
                    node: ast::ViewPathList(p.clone(), mine, b.clone()),
                    span: path.span,
                }))
            }

            // these are feature gated anyway
            ast::ViewPathGlob(_, id) => {
                if self.resolve_id(id, true, om, please_inline) { return None }
            }
        }
        Some(P(path.clone()))
    }

    fn resolve_id(&mut self, id: ast::NodeId, glob: bool,
                  om: &mut Module, please_inline: bool) -> bool {
        let tcx = match self.cx.maybe_typed {
            core::Typed(ref tcx) => tcx,
            core::NotTyped(_) => return false
        };
        let def = ast_util::def_id_of_def(*tcx.def_map.borrow().get(&id));
        if !ast_util::is_local(def) { return false }
        let analysis = match self.analysis {
            Some(analysis) => analysis, None => return false
        };
        if !please_inline && analysis.public_items.contains(&def.node) {
            return false
        }

        match tcx.map.get(def.node) {
            ast_map::NodeItem(it) => {
                if glob {
                    match it.node {
                        ast::ItemMod(ref m) => {
                            for vi in m.view_items.iter() {
                                self.visit_view_item(vi, om);
                            }
                            for i in m.items.iter() {
                                self.visit_item(&**i, om);
                            }
                        }
                        _ => { fail!("glob not mapped to a module"); }
                    }
                } else {
                    self.visit_item(it, om);
                }
                true
            }
            _ => false,
        }
    }

    pub fn visit_item(&mut self, item: &ast::Item, om: &mut Module) {
        debug!("Visiting item {:?}", item);
        match item.node {
            ast::ItemMod(ref m) => {
                om.mods.push(self.visit_mod_contents(item.span,
                                                     item.attrs.clone(),
                                                     item.vis,
                                                     item.id,
                                                     m,
                                                     Some(item.ident)));
            },
            ast::ItemEnum(ref ed, ref gen) =>
                om.enums.push(self.visit_enum_def(item, ed, gen)),
            ast::ItemStruct(ref sd, ref gen) =>
                om.structs.push(self.visit_struct_def(item, &**sd, gen)),
            ast::ItemFn(ref fd, ref pur, ref abi, ref gen, _) =>
                om.fns.push(self.visit_fn(item, &**fd, pur, abi, gen)),
            ast::ItemTy(ref ty, ref gen) => {
                let t = Typedef {
                    ty: ty.clone(),
                    gen: gen.clone(),
                    name: item.ident,
                    id: item.id,
                    attrs: item.attrs.clone(),
                    where: item.span,
                    vis: item.vis,
                };
                om.typedefs.push(t);
            },
            ast::ItemStatic(ref ty, ref mut_, ref exp) => {
                let s = Static {
                    type_: ty.clone(),
                    mutability: mut_.clone(),
                    expr: exp.clone(),
                    id: item.id,
                    name: item.ident,
                    attrs: item.attrs.clone(),
                    where: item.span,
                    vis: item.vis,
                };
                om.statics.push(s);
            },
            ast::ItemTrait(ref gen, _, ref tr, ref met) => {
                let t = Trait {
                    name: item.ident,
                    methods: met.clone(),
                    generics: gen.clone(),
                    parents: tr.clone(),
                    id: item.id,
                    attrs: item.attrs.clone(),
                    where: item.span,
                    vis: item.vis,
                };
                om.traits.push(t);
            },
            ast::ItemImpl(ref gen, ref tr, ref ty, ref meths) => {
                let i = Impl {
                    generics: gen.clone(),
                    trait_: tr.clone(),
                    for_: ty.clone(),
                    methods: meths.clone(),
                    attrs: item.attrs.clone(),
                    id: item.id,
                    where: item.span,
                    vis: item.vis,
                };
                om.impls.push(i);
            },
            ast::ItemForeignMod(ref fm) => {
                om.foreigns.push(fm.clone());
            }
            ast::ItemMac(ref _m) => {
                om.macros.push(Macro {
                    id: item.id,
                    attrs: item.attrs.clone(),
                    name: item.ident,
                    where: item.span,
                })
            }
        }
    }
}
