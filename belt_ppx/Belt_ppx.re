open Ppxlib;

class mapper = {
  as self;
  inherit class Ast_traverse.map as super;
  pub! expression = expr => {
    switch (expr.pexp_desc) {
    | Pexp_apply({pexp_desc: Pexp_ident({txt: Lident("|.")})}, [(Nolabel, obj_arg), (Nolabel, fn)]) =>
      let new_obj_arg = self#expression(obj_arg);
      switch (fn) {
      | {pexp_desc: Pexp_apply(fn, args), pexp_loc} =>
        let fn = self#expression(fn);
        let args = List.map(((lab, exp)) => (lab, self#expression(exp)), args);
        Ast_helper.Exp.apply(
          ~loc=expr.pexp_loc,
          fn,
          [(Nolabel, new_obj_arg), ...args],
        );
      | {pexp_desc: Pexp_construct(lident, None), pexp_loc, _} =>
        Ast_helper.Exp.construct(
          ~loc=expr.pexp_loc,
          lident,
          Some(new_obj_arg),
        );
      | _ => Ast_helper.Exp.apply(~loc=expr.pexp_loc, self#expression(fn), [(Nolabel, new_obj_arg)]);
      };
    | _ => super#expression(expr)
    };
  };
};

let structure_mapper = s => (new mapper)#structure(s)

let () =
  Ppxlib.Driver.register_transformation(
    ~preprocess_impl=structure_mapper,
    "ppx_belt",
  );
