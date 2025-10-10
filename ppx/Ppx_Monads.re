
/**
Things I would like:

// maybe this is overkill? also probably harder to parse
switch%opt (somethingOptional) {
| theContents =>
};

// so each non-wildcard branch is wrapped in `Some`. Is this too weird?
switch%orNone (x) {
  | each => case
  | doesntNeed => toBe
  | aSome => atTheEnd
  | _ => None
}

Alsoooo I really want to be able to provide
hover-for-explanation for %ppx extension points.
How could I do that in a general way?

Done!!! As long as the ppx drops a `[@ocaml.explanation "some text"]`
somewhere, the `loc` of attribute's `loc(string)` bit will be used to
show the hover text that is the context of the attribute.

[@ocaml.explanation {|

```
let%opt name = value;
otherStuff
```
is transformed into
```
switch (value) {
  | None => None
  | Some(name) =>
    otherStuff
}
```
This means that `otherStuff` needs to end with an optional.

If you want `otherStuff` to be automatically wrapped in `Some()`,
then use `let%opt_wrap`.
Alternatively, if you are just performing a side effect, and want
the result of the whole thing to be unit, use `let%consume`.
|}]

 */

open Ppxlib;

/***
 * https://ocsigen.org/lwt/dev/api/Ppx_lwt
 * https://github.com/zepalmer/ocaml-monadic
 */
let fail = (loc, txt) => raise(Location.Error(Location.Error.make(~loc, ~sub=[], txt)));

let rec process_bindings = (bindings) =>
  Parsetree.(
    switch bindings {
    | [] => assert false
    | [binding] => (binding.pvb_pat, binding.pvb_expr)
    | [binding, ...rest] =>
      let (pattern, expr) = process_bindings(rest);
      (
        Ast_helper.Pat.tuple([binding.pvb_pat, pattern]),
        Ast_helper.Exp.tuple(~loc=binding.pvb_expr.pexp_loc, [binding.pvb_expr, expr])
      )
    }
  );

let opt_explanation = {|
Optional declaration sugar:
```
let%opt name = value;
otherStuff
```
is transformed into
```
switch (value) {
| None => None
| Some(name) =>
  otherStuff
}
```
This means that `otherStuff` needs to have type `option`.

If you want `otherStuff` to be automatically wrapped in `Some()`,
then use `let%opt_wrap`.
Alternatively, if you are just performing a side effect, and want
the result of the whole thing to be unit, use `let%consume`.
|};

let opt_wrap_explanation = {|
Optional declaration sugar:
```
let%opt_wrap name = value;
otherStuff
```
is transformed into
```
switch (value) {
| None => None
| Some(name) => Some({
    otherStuff
  })
}
```
The `wrap` suffix means that the `otherStuff` will be automatically
wrapped in a `Some`.

If you don't want this wrapping, then use `let%opt`.
Alternatively, if you are just performing a side effect, and want
the result of the whole thing to be unit, use `let%consume`.
|};

let opt_consume_explanation = {|
Optional declaration sugar:
```
let%consume name = value;
otherStuff
```
is transformed into
```
switch (value) {
| None => ()
| Some(name) =>
  otherStuff
}
```
This is intented for performing side-effects only -- `otherStuff`
must end up as type `unit`.
|};

let extractor = Ast_pattern.(single_expr_payload(pexp_let(nonrecursive, __, __)));

let expander = (name, replacement, explanation, ~ctxt as context, valueBindings, continuation) => {
  let loc = Expansion_context.Extension.extension_point_loc(context);
  let (pat, expr) = process_bindings(valueBindings);
  Ast_helper.Exp.attr(
    Ast_helper.Exp.apply(~loc, replacement(loc), [(Nolabel, expr), (Labelled("f"), Ast_helper.Exp.fun_(~loc,  Nolabel, None, pat, continuation))]),
    Ast_helper.Attr.mk(
      ~loc=expr.pexp_loc,
      {txt: "ocaml.explanation", loc},
      PStr([Ast_helper.Str.eval(Ast_helper.Exp.constant(Pconst_string(explanation, loc, None)))])
    )
  )
};

let rule = ((name, replacement, explanation)) => 
  Context_free.Rule.extension(Extension.V3.declare(name, Extension.Context.expression, extractor, expander(name, replacement, explanation)));

let rules = List.map(rule, [
  ("opt", loc => [%expr Monads.Option.bind], opt_explanation),
  ("opt_wrap", loc => [%expr Monads.Option.map], opt_wrap_explanation),
  ("opt_consume", loc => [%expr Monads.Option.consume], opt_consume_explanation),
  ("opt_force", loc => [%expr Monads.Option.force], "Force an optional. Throws an error if None"),
  ("try", loc => [%expr Monads.Result.bind], "Sugar for the Result type"),
  ("try_wrap", loc => [%expr Monads.Result.map], "Sugar for the Result type - auto-wraps in `Ok()`"),
  ("try_consume", loc => [%expr Monads.Result.consume], "Sugar for the Result type - side-effectful version"),
  ("try_force", loc => [%expr Monads.Result.force], "Sugar for the Result type - force a result"),
  ("await", loc => [%expr Monads.Promise.bind], "Sugar for Promises"),
  ("await_wrap", loc => [%expr Monads.Promise.map], "Sugar for Promises - auto-wraps in `Promise.resolve`"),
  ("await_consume", loc => [%expr Monads.Promise.consume], "Sugar for Promises - just for side effects. Throws on error"),
]);

let () =
  Ppxlib.Driver.register_transformation(
    ~rules,
    "ppx_monads",
  );
