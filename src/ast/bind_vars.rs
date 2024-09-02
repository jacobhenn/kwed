use super::{
    desugared::{Expr, Item, Module},
    Ident,
};

use std::rc::Rc;

use uuid::Uuid;

// TODO: change to Rc instead of Box would make it a little nicer
#[derive(Debug, Clone)]
enum Context {
    Empty,
    Var {
        outer: Box<Self>,
        name: Ident,
        id: Uuid,
    },
}

impl Context {
    fn id(&self, search_name: &Ident) -> Option<Uuid> {
        match self {
            Context::Empty => None,
            Context::Var { outer, name, id } => {
                if name == search_name {
                    Some(*id)
                } else {
                    outer.id(search_name)
                }
            }
        }
    }
}

impl Expr {
    fn bind_vars(&mut self, ctx: &Context) {
        match self {
            Expr::TypeType { .. } | Expr::Var { .. } => (),
            Expr::Displace { arg, .. } => Rc::make_mut(arg).bind_vars(ctx),
            Expr::Path { path, span } => {
                if let [name] = &mut path.components[..] {
                    if let Some(id) = ctx.id(name) {
                        *self = Self::Var {
                            id,
                            name: name.clone(),
                            span: span.clone(),
                        };
                    }
                }
            }
            Expr::Fn { param, body, .. } => {
                Rc::make_mut(param).ty.bind_vars(&ctx);

                let ctx = Context::Var {
                    outer: Box::new(ctx.clone()),
                    name: param.name.clone(),
                    id: param.id,
                };

                Rc::make_mut(body).bind_vars(&ctx);
            }
            Expr::FnType { param, cod, .. } => {
                Rc::make_mut(param).ty.bind_vars(ctx);

                let ctx = Context::Var {
                    outer: Box::new(ctx.clone()),
                    name: param.name.clone(),
                    id: param.id,
                };

                Rc::make_mut(cod).bind_vars(&ctx);
            }
            Expr::FnApp { func, arg, .. } => {
                Rc::make_mut(func).bind_vars(ctx);
                Rc::make_mut(arg).bind_vars(ctx);
            }
        }
    }
}

impl Item {
    pub fn bind_vars(&mut self) {
        match self {
            Item::Def { ty, val, .. } => {
                ty.bind_vars(&Context::Empty);
                val.bind_vars(&Context::Empty);
            }
            Item::Axiom { ty, .. } => ty.bind_vars(&Context::Empty),
            Item::Inductive {
                params,
                ty,
                constructors,
                ..
            } => {
                let mut ctx = Context::Empty;
                for param in params {
                    param.ty.bind_vars(&ctx);
                    ctx = Context::Var {
                        outer: Box::new(ctx),
                        name: param.name.clone(),
                        id: param.id,
                    };
                }

                ty.bind_vars(&ctx);

                for (_name, ty) in constructors {
                    ty.bind_vars(&ctx);
                }
            }
        }
    }
}

impl Module {
    pub fn bind_vars(&mut self) {
        for item in self.items.values_mut() {
            item.bind_vars();
        }
    }
}
