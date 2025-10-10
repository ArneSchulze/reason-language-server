open Compiler_libs_406;

type envContext = [
  | `Type
  | `Module
  | `ModuleType
  | `Value
  | `Const
  | `Class
  | `ClassType
];

type additionalContext = [
  | `Method
  | `Field
];

type context = [
  | envContext
  | additionalContext
];

type additionalLookup = {
  context: additionalContext,
  name: string
}

type lookupPath = {
  envContext: option(envContext),
  envPath: option(Longident.t),
  additionalLookup: option(additionalLookup),
}

let rec keep_some_list = (l, acc) => 
  switch (l) {
    | [] => List.rev(acc)
    | [Some(x), ...rest] => keep_some_list(rest, [x, ...acc])
    | [None, ...rest] => keep_some_list(rest, acc)
  }

let lident_to_string = l => l |> Longident.flatten |> String.concat(".")

let findInEnv = (env: Env.t, name: Longident.t, context: option(envContext)) => {
  let env = try (Envaux.env_of_only_summary(env)) {
    | _ => env
  };

  let maybeType = 
    switch (env |> Env.lookup_type(name)) {
      | p =>
        Some((env |> Env.find_type(p)).type_loc)
      | exception _ => None
    };
  let maybeValue =
    switch (env |> Env.lookup_value(name)) {
      | (_, desc) => Some(desc.val_loc)
      | exception _ => None
    };
  let maybeModule =
    switch (env |> Env.lookup_module(~load=true, name)) {
      | p =>
        Some((env |> Env.find_module(p)).md_loc)
      | exception _ => None
    };
  let maybeModtype =
    switch (env |> Env.lookup_modtype(name)) {
      | (_p, mt) => Some(mt.mtd_loc)
      | exception _ => None
    };
  let maybeClass =
    switch (env |> Env.lookup_class(name)) {
      | (_p, c) => Some(c.cty_loc)
      | exception _ => None
    };
  let maybeClassType =
    switch (env |> Env.lookup_cltype(name)) {
      | (_p, ct) => Some(ct.clty_loc)
      | exception _ => None
    };
  let maybeConstructor =
    switch (env |> Env.lookup_constructor(name)) {
      | c => Some(c.cstr_loc)
      | exception _ => None
    };
  let maybeLabel =
    switch (env |> Env.lookup_label(name)) {
      | l => Some(l.lbl_loc)
      | exception _ => None
    };

  let l = [maybeType, maybeValue, maybeConstructor, maybeModule, maybeModtype, maybeClass, maybeClassType, maybeLabel];

  let l = 
    switch (context) {
      | None => l
      | Some(context) =>
        switch (context) {
        | `Type => [maybeType, ...l]
        | `Value => [maybeValue, ...l]
        | `Module => [maybeModule, ...l]
        | `ModuleType => [maybeModtype, ...l]
        | `Const => [maybeConstructor, ...l]
        | `Class => [maybeClass, ...l]
        | `ClassType => [maybeClassType, ...l]
      };
    }

  switch (keep_some_list(l, [])) {
    | [] => None
    | [loc, ..._] => Some(loc)
  } 
}

let rec signatureFromClassType: Types.class_type => Types.class_signature = 
  fun
  | Cty_constr(_, _, cty) => signatureFromClassType(cty)
  | Cty_signature(s) => s
  | Cty_arrow(_, _, cty) => signatureFromClassType(cty);

let rec findAdditionalInEnv = (env: Env.t, name: Longident.t, contextType: option(additionalContext), additional: string) => {
  switch (contextType) {
    | Some(`Field) => 
      switch (env |> Env.lookup_label(Longident.Ldot(name, additional))) {
        | l => Some(l.lbl_loc)
        | exception _ => 
          switch (env |> Env.lookup_type(name)) {
          | p =>
            switch (env |> Env.find_type(p)) {
              | {type_kind: Types.Type_record(labels, _), type_loc} =>
              let maybeLabel = labels |> List.find_opt(l => l.Types.ld_id->Ident.name == additional);
              switch (maybeLabel) {
                | Some(label) => Some(label.ld_loc)
                | None => None
              }
              | _ => None
            };
          | exception _ => None
        }
      }
      
    | Some(`Method) =>
      switch (env |> Env.lookup_label(Longident.Ldot(name, additional))) {
        | l => Some(l.lbl_loc)
        | exception _ => 
          switch (env |> Env.lookup_class(name)) {
          | (_p, {cty_loc}) => Some(cty_loc)
          | exception _ => 
            switch (env |> Env.lookup_cltype(name)) {
              | (_p, {clty_loc}) => Some(clty_loc)
              | exception _ => None
            }
        }
      }
    | None =>
      switch (findAdditionalInEnv(env, name, Some(`Field), additional)) {
        | Some(_) as loc => loc
        | None => findAdditionalInEnv(env, name, Some(`Method), additional)
      }
  }
}

let findInEnvs = (envs: list(Env.t), lookupPath) => {
  let rec auxAdditional = (envs, name, contextType, additional) =>
    switch (envs) {
      | [] => None
      | [env, ...rest] => 
        switch (findAdditionalInEnv(env, name, contextType, additional)) {
          | Some(loc) => Some(loc)
          | None => auxAdditional(rest, name, contextType, additional)
        }
    };
  let rec aux = (envs, name, contextType) => 
    switch (envs) {
      | [] => None
      | [env, ...rest] => 
        switch (findInEnv(env, name, contextType)) {
          | Some(loc) => Some(loc)
          | None => aux(rest, name, contextType)
        }
    };

  switch (lookupPath.envPath) {
    | None => None
    | Some(path) =>
      switch (lookupPath.additionalLookup) {
        | None =>
          switch (lookupPath.envContext) {
            | Some(ctx) => aux(envs, path, Some(ctx))
            | None =>
              switch (aux(envs, path, None)) {
                | Some(_) as loc => loc
                | None => 
                  switch (path) {
                    | Longident.Ldot(p, name) => auxAdditional(envs, p, None, name)
                    | _ => None
                  };
              }
          }
        | Some(additionalCtx) =>
          auxAdditional(envs, path, Some(additionalCtx.context), additionalCtx.name);
      }
  }
};

let locToUri = (thisFile: string, loc: Location.t) => {
  let loc = loc.loc_start;
  let filename = if (loc.pos_fname == "") {
    thisFile
  } else {
    loc.pos_fname
  };
  let realFilename = try (Unix.realpath(filename)) {
      | _exn => filename
    };
  let lineNumber = loc.pos_lnum;
  let columnNumber = loc.pos_cnum - loc.pos_bol;

  "file://" ++ realFilename ++ "#L" ++ string_of_int(lineNumber) ++ "%2C" ++ string_of_int(columnNumber)
}