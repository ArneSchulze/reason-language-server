
open Compiler_libs_406;
open Typedtree;
open SharedTypes;
open Infix;
open EnvUtils;
open OdocUtils;

let handleConstructor = (path, txt) => {
  let typeName =
    switch path {
    | Path.Pdot(_path, typename, _) => typename
    | Pident(ident) => Ident.name(ident)
    | _ => assert false
    };
  Longident.(
    switch txt {
    | Longident.Lident(name) => (name, Lident(typeName))
    | Ldot(left, name) => (name, Ldot(left, typeName))
    | Lapply(_, _) => assert false
    }
  )
};

let rec relative = (ident, path) =>
  switch (ident, path) {
  | (Longident.Lident(name),
     Path.Pdot(path, pname, _))
    when pname == name =>
    Some(path)
  | (Longident.Ldot(ident, name),
     Path.Pdot(path, pname, _))
    when pname == name =>
    relative(ident, path)
  /* | (Ldot(Lident("*predef*" | "exn"), _), Pident(_)) => None */
  | _ => None
  };

let addOpen = (extra, path, loc, extent, ident) => {
  let op = {path, loc, used: [], extent, ident};
  Hashtbl.add(extra.opens, loc, op);
};

let findClosestMatchingOpen = (opens, path, ident, loc) => {
  let%opt openNeedle = relative(ident, path);

  let matching = Hashtbl.fold((_, op, res) => {
    if (Utils.locWithinLoc(loc, op.extent) && Path.same(op.path, openNeedle)) {
      [op, ...res]
    } else {
      res
    }
  }, opens, []) |. Belt.List.sort((a, b) => {
    open Location;
    b.loc.loc_start.pos_cnum - a.loc.loc_start.pos_cnum
  });

  switch matching {
    | [] => None
    | [first, ..._] => Some(first)
  }
};

let getTypeAtPath = (~env, path) => {
  switch (Query.fromCompilerPath(~env, path)) {
  | `GlobalMod(_) => `Not_found
  | `Global(moduleName, path) => `Global(moduleName, path)
  | `Not_found => `Not_found
  | `Exported(env, name) => {
      let res = {
        let%opt stamp = Query.hashFind(env.exported.types, name);
        let%opt_wrap declaredType = Query.hashFind(env.file.stamps.types, stamp);
        `Local(declaredType)
      };
      res |? `Not_found
  }
  | `Stamp(stamp) => {
    let res = {
      let%opt_wrap declaredType = Query.hashFind(env.file.stamps.types, stamp);
      `Local(declaredType)
    };
    res |? `Not_found
  }
  }
};

module F = (Collector: {
  let filepath: string;

  let extra: extra;
  let file: file;
  let scopeExtent: ref(list(Location.t));

  let envs: ref(list(Env.t));

  let allLocations: bool;

  let processDoc: (~location: Compiler_libs_406.Location.t, ~resolveLink: string => (option(string), string), string) => string;
}) => {
  let extra = Collector.extra;
  let file = Collector.file;
  let filepath = Collector.filepath;

  let envs = Collector.envs;
  let lastEnvs = ref([]);

  let addEnv = env => {
    envs := [env, ...envs^];
    lastEnvs := [envs^, ...lastEnvs^];
  };

  let addEnvs = env => {
    envs := List.concat([env, envs^]);
    lastEnvs := [envs^, ...lastEnvs^];
  }

  let resetEnv = env => {
    switch (lastEnvs^) {
      | [hd, ...tail] =>
        envs := hd;
        lastEnvs := tail;
      | [] =>
        envs := [];
        lastEnvs := [];
    }
  }

  let rec unwind_lident = (l, ps) =>
    switch (l) {
      | Longident.Lident(n) => [n, ...ps]
      | Longident.Ldot(inner, name) => unwind_lident(inner, [name, ...ps])
      | Longident.Lapply(_, _) => assert false
    }

  let rec wind_lident = (ps, l) => {
    switch (ps, l) {
      | ([], _) => 
        l |> Option.get
      | ([name, ...rest], _) =>
        switch (l) {
          | None => wind_lident(rest, Some(Longident.Lident(name)))
          | Some(acc) => wind_lident(rest, Some(Longident.Ldot(acc, name)))
        }
    }
  }

  let resolveWithEnvs = (unparsed) => {
  switch (parseReference(unparsed)) {
    | None => (None, unparsed)
    | Some(lookupPath) => 
      let res = findInEnvs(envs^, lookupPath) |?>> locToUri(filepath);
      
      let res =
        switch (res) {
          | None => 
            let lookupPath = {
              ...lookupPath,
              envPath: switch (lookupPath.envPath) {
                | Some(l) => Some(wind_lident([file.moduleName, ...unwind_lident(l, [])], None))
                | None => Some(Longident.Lident(file.moduleName))
              }
            }
            findInEnvs(envs^, lookupPath) |?>> locToUri(filepath);
          | Some(_) as res => res
        };

      (res, lookupPath.envPath->Belt.Option.mapWithDefault(lookupPath.additionalLookup->Belt.Option.mapWithDefault(unparsed, add => add.name), p => {
        let p = lident_to_string(p);
        lookupPath.additionalLookup->Belt.Option.mapWithDefault(p, add => p ++ "." ++ add.name)
      }));
    };
  }

  let processDoc = Collector.processDoc(~resolveLink=resolveWithEnvs);

  let maybeAddUse = (path, ident, loc, tip) => {
    let%opt_consume tracker = findClosestMatchingOpen(extra.opens, path, ident, loc);
    let%opt_consume relpath = Query.makeRelativePath(tracker.path, (path));

    tracker.used = [(relpath, tip, loc), ...tracker.used];
  };

  let addLocation = (loc, ident) => extra.locations = [(loc, ident), ...extra.locations];
  let addReference = (stamp, loc) => Hashtbl.replace(extra.internalReferences, stamp, [loc, ...Hashtbl.mem(extra.internalReferences, stamp) ? Hashtbl.find(extra.internalReferences, stamp) : []]);
  let addExternalReference = (moduleName, path, tip, loc) => {
    /* TODO need to follow the path, and be able to load the files to follow module references... */
    Hashtbl.replace(extra.externalReferences, moduleName, [(path, tip, loc), ...Hashtbl.mem(extra.externalReferences, moduleName) ? Hashtbl.find(extra.externalReferences, moduleName) : []]);
  };
  let env = {Query.file: Collector.file, exported: Collector.file.contents.exported};

  let getTypeAtPath = getTypeAtPath(~env);

  let addForPathModule = (path, lident, loc, tip) => {
    maybeAddUse(path, lident, loc, tip);
    let identName = Longident.last(lident);
    let identLoc = Utils.endOfLocation(loc, String.length(identName));
    let path = (path);
    let locType = switch (Query.fromCompilerPath(~env, path)) {
      | `Stamp(stamp) => {
        addReference(stamp, identLoc);
        Loc.LocalReference(stamp, tip);
      }
      | `Not_found => Loc.NotFound
      | `Global(moduleName, path) => {
        addExternalReference(moduleName, path, tip, identLoc);
        Loc.GlobalReference(moduleName, path, tip)
      }
      | `Exported(env, name) => {
        let res = {
          let%opt_wrap stamp = Query.hashFind(env.exported.values, name);
          addReference(stamp, identLoc);
          Loc.LocalReference(stamp, tip)
        };
        res |? Loc.NotFound
      }
      | `GlobalMod(_) => Loc.NotFound
    };
    addLocation(loc, Loc.Module(locType));
  };

  let addForPath = (path, lident, loc, typ, tip) => {
    maybeAddUse(path, lident, loc, tip);
    let identName = Longident.last(lident);
    let identLoc = Utils.endOfLocation(loc, String.length(identName));
    let path = (path);
    let locType = switch (Query.fromCompilerPath(~env, path)) {
      | `Stamp(stamp) => {
        addReference(stamp, identLoc);
        Loc.LocalReference(stamp, tip);
      }
      | `Not_found => Loc.NotFound
      | `Global(moduleName, path) => {
        addExternalReference(moduleName, path, tip, identLoc);
        Loc.GlobalReference(moduleName, path, tip)
      }
      | `Exported(env, name) => {
        let res = {
          let%opt_wrap stamp = Query.hashFind(env.exported.values, name);
          addReference(stamp, identLoc);
          Loc.LocalReference(stamp, tip)
        };
        res |? Loc.NotFound
      }
      | `GlobalMod(_) => Loc.NotFound
    };
    addLocation(loc, Loc.Typed(typ, locType));
  };

  let addForPathParent = (path, loc) => {
    let locType = switch (Query.fromCompilerPath(~env, path)) {
      | `GlobalMod(name) =>
        /* TODO track external references to filenames to handle renames well */
        Loc.TopLevelModule(name)
      | `Stamp(stamp) => {
        addReference(stamp, loc);
        Module(LocalReference(stamp, Module))
      }
      | `Not_found => Module(NotFound)
      | `Global(moduleName, path) => {
        addExternalReference(moduleName, path, Module, loc);
        Module(GlobalReference(moduleName, path, Module))
      }
      | `Exported(env, name) => {
        let res = {
          let%opt_wrap stamp = Query.hashFind(env.exported.modules, name);
          addReference(stamp, loc);
          Loc.Module(LocalReference(stamp, Module))
        };
        res |? Module(NotFound)
      }
    };
    addLocation(loc, locType);
  };

  let addForField = (recordType, item, {Asttypes.txt, loc}) => {
    switch (Shared.dig(recordType).desc) {
      | Tconstr(path, _args, _memo) => {
        let t = getTypeAtPath((path));
        let {Types.lbl_res} = item;

        let (name, typeLident) = handleConstructor(path, txt);
        maybeAddUse(path, typeLident, loc, Attribute(name));

        let nameLoc = Utils.endOfLocation(loc, String.length(name));
        let locType = switch (t) {
          | `Local({stamp, contents: {kind: Record(attributes)}}) => {
            {
              let%opt_wrap {stamp: astamp} = Belt.List.getBy(attributes, a => a.name.txt == name);
              addReference(astamp, nameLoc);
              Loc.LocalReference(stamp, Attribute(name));
            } |? Loc.NotFound
          }
          | `Global(moduleName, path) =>
            addExternalReference(moduleName, path, Attribute(name), nameLoc);
            Loc.GlobalReference(moduleName, path, Attribute(name))
          | _ => Loc.NotFound
        };
        addLocation(nameLoc, Loc.Typed(Shared.makeFlexible(lbl_res), locType))
      }
      | _ => ()
    }
  };

  let addForRecord = (recordType, items) => {
    switch (Shared.dig(recordType).desc) {
      | Tconstr(path, _args, _memo) => {
        let t = getTypeAtPath((path));
        items |> List.iter((({Asttypes.txt, loc}, {Types.lbl_res}, _)) => {
          /* let name = Longident.last(txt); */

          let (name, typeLident) = handleConstructor(path, txt);
          maybeAddUse(path, typeLident, loc, Attribute(name));

          let nameLoc = Utils.endOfLocation(loc, String.length(name));
          let locType = switch (t) {
            | `Local({stamp, contents: {kind: Record(attributes)}}) => {
              {
                let%opt_wrap {stamp: astamp} = Belt.List.getBy(attributes, a => a.name.txt == name);
                addReference(astamp, nameLoc);
                Loc.LocalReference(stamp, Attribute(name));
              } |? Loc.NotFound
            }
            | `Global(moduleName, path) =>
              addExternalReference(moduleName, path, Attribute(name), nameLoc);
              Loc.GlobalReference(moduleName, path, Attribute(name))
            | _ => Loc.NotFound
          };
          addLocation(nameLoc, Loc.Typed(Shared.makeFlexible(lbl_res), locType))
        })
      }
      | _ => ()
    }
  };

  let addForConstructor = (constructorType, {Asttypes.txt, loc}, {Types.cstr_name}) => {
    switch (Shared.dig(constructorType).desc) {
      | Tconstr(path, _args, _memo) => {
        /* let name = Longident.last(txt); */

        let (name, typeLident) = handleConstructor(path, txt);
        maybeAddUse(path, typeLident, loc, Constructor(name));

        let nameLoc = Utils.endOfLocation(loc, String.length(name));
        let t = getTypeAtPath((path));
        let locType = switch (t) {
          | `Local({stamp, contents: {kind: Variant(constructos)}}) => {
            {
              let%opt_wrap {stamp: cstamp} = Belt.List.getBy(constructos, a => a.name.txt == cstr_name);
              addReference(cstamp, nameLoc);
              Loc.LocalReference(stamp, Constructor(name))
            } |? Loc.NotFound
          }
          | `Global(moduleName, path) =>
            addExternalReference(moduleName, path, Constructor(name), nameLoc);
            Loc.GlobalReference(moduleName, path, Constructor(name))
          | _ => Loc.NotFound
        };
        addLocation(nameLoc, Loc.Typed(Shared.makeFlexible(constructorType), locType));
      }
      | _ => ()
    }
  };

  let currentScopeExtent = () => {
    if (Collector.scopeExtent^ == []) {
      Location.none
    } else {
      List.hd(Collector.scopeExtent^);
    }
  };
  let addScopeExtent = loc => Collector.scopeExtent := [loc, ...Collector.scopeExtent^];
  let popScopeExtent = () => if (List.length(Collector.scopeExtent^) > 1) {
    Collector.scopeExtent := List.tl(Collector.scopeExtent^);
  };

  let rec addForLongident = (top, path: Path.t, txt: Longident.t, loc) => {
    if (!loc.Location.loc_ghost) {
      let idLength = String.length(String.concat(".", Longident.flatten(txt)));
      let reportedLength = loc.loc_end.pos_cnum - loc.loc_start.pos_cnum;
      let isPpx = idLength != reportedLength;
      if (isPpx) {
        switch (top) {
          | Some((t, tip)) => addForPath(path, txt, loc, t, tip)
          | None => addForPathParent((path), loc)
          }
      } else {
        let l = Utils.endOfLocation(loc, String.length(Longident.last(txt)));
        switch (top) {
          | Some((t, tip)) => addForPath(path, txt, l, t, tip)
          | None => addForPathParent((path), l)
        };
        switch (path, txt) {
          | (Pdot(pinner, _pname, _), Ldot(inner, name)) => {
            addForLongident(None, pinner, inner, Utils.chopLocationEnd(loc, String.length(name) + 1));
          }
          | (Pident(_), Lident(_)) => ()
          | _ => ()
        };
      };
    }
  };

  let rec handle_module_expr = expr => switch expr {
    | Tmod_constraint(expr, _, _, _) => handle_module_expr(expr.mod_desc)
    | Tmod_ident(path, {txt, loc}) =>
      Log.log("Ident!! " ++ String.concat(".", Longident.flatten(txt)));
      maybeAddUse(path, txt, loc, Module);
      addForLongident(None, path, txt, loc);
    | Tmod_functor(_ident, _argName, _maybeType, resultExpr) =>
      handle_module_expr(resultExpr.mod_desc)
    | Tmod_apply(obj, arg, _) =>
      handle_module_expr(obj.mod_desc);
      handle_module_expr(arg.mod_desc);
    | _ => ()
  };

  let rec handle_module_typ = expr => switch expr {
    | Tmod_constraint(expr, _, _, _) => handle_module_expr(expr.mod_desc)
    | Tmod_ident(path, {txt, loc}) =>
      Log.log("Ident!! " ++ String.concat(".", Longident.flatten(txt)));
      maybeAddUse(path, txt, loc, Module);
      addForLongident(None, path, txt, loc);
    | Tmod_functor(_ident, _argName, _maybeType, resultExpr) =>
      handle_module_expr(resultExpr.mod_desc)
    | Tmod_apply(obj, arg, _) =>
      handle_module_expr(obj.mod_desc);
      handle_module_expr(arg.mod_desc);
    | _ => ()
  };

  open Typedtree;
  include TypedtreeIter.DefaultIteratorArgument;
  let enter_structure_item = item => {
    addEnv(item.str_env);
    switch (item.str_desc) {
    | Tstr_attribute(({Asttypes.txt: "ocaml.explanation", loc}, PStr([{pstr_desc: Pstr_eval({pexp_desc: Pexp_constant(
        Pconst_string
        (doc, _))}, _)}]))) => {
      addLocation(loc, Loc.Explanation(doc))
    }
    | Tstr_include({incl_mod: expr}) => {
      addEnv(expr.mod_env);
      handle_module_expr(expr.mod_desc);
      resetEnv();
    }
    | Tstr_module({mb_expr}) =>
      addEnv(mb_expr.mod_env);
      handle_module_expr(mb_expr.mod_desc);
      resetEnv();
    | Tstr_recmodule(mod_list) => mod_list |> List.iter(({mb_expr}) => {
        addEnv(mb_expr.mod_env);
        handle_module_expr(mb_expr.mod_desc);
        resetEnv()
      })
    | Tstr_open({open_path, open_txt: {txt, loc} as l}) => {
      /* Log.log("Have an open here"); */
      maybeAddUse(open_path, txt, loc, Module);
      let tracker = {
        path: (open_path),
        loc,
        ident: l,
        used: [],
        extent: {
          loc_ghost: true,
          loc_start: loc.loc_end,
          loc_end: currentScopeExtent().loc_end,
        }
      };
      addForLongident(None, open_path, txt, loc);
      Hashtbl.replace(Collector.extra.opens, loc, tracker);
    }
    | _ => ()
    }
  };

  let leave_structure_item = _ => {
    resetEnv();
  }

  let enter_structure = ({str_items, str_final_env}) => {
    addEnv(str_final_env);
    if (str_items != []) {
      let first = List.hd(str_items);
      let last = List.nth(str_items, List.length(str_items) - 1);

      let extent = {
        Location.loc_ghost: true,
        loc_start: first.str_loc.loc_start,
        loc_end: last.str_loc.loc_end,
      };

      addScopeExtent(extent);
    };
  };

  let leave_structure = str => {
    if (str.str_items != []) {
      popScopeExtent();
    }
    resetEnv();
  };

  let enter_signature_item = (item) => {
    addEnv(item.sig_env);
    switch (item.sig_desc) {
    | Tsig_value({val_id, val_loc, val_name: name, val_desc, val_attributes}) => {
      let stamp = Ident.binding_time(val_id);
      if (!Hashtbl.mem(Collector.file.stamps.values, stamp)) {
        let declared = ProcessAttributes.newDeclared(
          ~name,
          ~stamp,
          ~extent=val_loc,
          ~scope={
            loc_ghost: true,
            loc_start: val_loc.loc_end,
            loc_end: currentScopeExtent().loc_end,
          },
          ~modulePath=NotVisible,
          ~processDoc=processDoc,
          ~contents={Value.typ: Shared.makeFlexible(val_desc.ctyp_type), recursive: false},
          false,
          List.concat([val_attributes, val_desc.ctyp_attributes])
        );
        Hashtbl.add(Collector.file.stamps.values, stamp, declared);
        addReference(stamp, name.loc);
        addLocation(name.loc, Loc.Typed(Shared.makeFlexible(val_desc.ctyp_type), Loc.Definition(stamp, Value)));
      }
    }
    | Tsig_include({incl_mod}) => {
        switch (incl_mod.mty_desc) {
        | Tmty_ident(path, ident)
        | Tmty_alias(path, ident) =>
          addForPathModule(path, ident.txt, ident.loc, Module);
        | Tmty_with(mod_type, constraints) => 
          constraints |> List.iter(((path, ident: Location.loc(Longident.t), c)) => {switch c {
            | Twith_type(typ_decl)
            | Twith_typesubst(typ_decl) =>
              switch (typ_decl.typ_type.type_manifest) {
                | None => ()
                | Some(typ) =>
                  addForPath(path, ident.txt, ident.loc, Shared.makeFlexible(typ), Type)
              }
            | Twith_module(path, ident)
            | Twith_modsubst(path, ident) =>
              addForPathModule(path, ident.txt, ident.loc, Module);
          }});
          switch (mod_type.mty_desc) {
            | Tmty_ident(path, ident) => addForPathModule(path, ident.txt, ident.loc, ModuleType);
            | Tmty_alias(path, ident) => addForPathModule(path, ident.txt, ident.loc, ModuleType);
            | _ => ()
          }
        | _ => ()
        }
    }
    | _ => ()
    };
  }

  let leave_structure_item = _ => {
    resetEnv();
  };

  let enter_core_type = ({ctyp_type, ctyp_desc, ctyp_env}) => {
    addEnv(ctyp_env);
    switch (ctyp_desc) {
      | Ttyp_constr(path, {txt, loc}, _args) => {
        /* addForPath(path, txt, loc, Shared.makeFlexible(ctyp_type), Type) */
        addForLongident(
          Some((Shared.makeFlexible(ctyp_type), Type)),
          path,
          txt, loc);
      }
      | _ => ()
    }
  };

  let leave_core_type = _ => {
    resetEnv();
  };


  let enter_pattern = ({pat_desc, pat_loc, pat_type, pat_attributes, pat_env}) => {
    addEnv(pat_env);
    let addForPattern = (stamp, name) => {
        if (!Hashtbl.mem(Collector.file.stamps.values, stamp)) {
          let declared = ProcessAttributes.newDeclared(
            ~name,
            ~stamp,
            ~scope={
              loc_ghost: true,
              loc_start: pat_loc.loc_end,
              loc_end: currentScopeExtent().loc_end,
            },
            ~modulePath=NotVisible,
            ~extent=pat_loc,
            ~processDoc=processDoc,
            ~contents={Value.typ: Shared.makeFlexible(pat_type), recursive: false},
            false,
            pat_attributes
          );
          Hashtbl.add(Collector.file.stamps.values, stamp, declared);
          addReference(stamp, name.loc);
          addLocation(name.loc, Loc.Typed(Shared.makeFlexible(pat_type), Loc.Definition(stamp, Value)));
        }
    };
    /* Log.log("Entering pattern " ++ Utils.showLocation(pat_loc)); */
    switch (pat_desc) {
      | Tpat_record(items, _) => {
        addForRecord(pat_type, items);
      }
      | Tpat_construct(lident, constructor, _) => {
        addForConstructor(pat_type, lident, constructor)
      }
      | Tpat_alias(_inner, ident, name) => {
        let stamp = Ident.binding_time(ident);
        addForPattern(stamp, name);
      }
      | Tpat_var(ident, name) => {
        /* Log.log("Pattern " ++ name.txt); */
        let stamp = Ident.binding_time(ident);
        addForPattern(stamp, name);
      }
      | _ => ()
    };
    if (Collector.allLocations) {
      addLocation(pat_loc, Loc.Typed(Shared.makeFlexible(pat_type), Loc.NotFound));
    };
  };

  let leave_pattern = _ => {
    resetEnv();
  };

  let enter_expression = expression => {
    addEnv(expression.exp_env);
    expression.exp_extra |. Belt.List.forEach(((e, eloc, _)) => switch e {
      | Texp_open(_, path, ident, _) => {
        extra.opens |. Hashtbl.add(eloc, {
          path: (path),
          ident,
          loc: eloc,
          extent: expression.exp_loc,
          used: [],
        })
      }
      | _ => ()
    });
    switch (expression.exp_desc) {
    /* | Texp_apply({exp_desc: Pexp_ident(_, {txt: Ldot(Lident("ReasonReact"), "element")})}, [(_, {exp_desc: Pexp_apply({exp_desc: Pexp_ident(_, {txt})}, _)})]) =>{

    } */
    | Texp_ident(path, {txt, loc}, {val_type}) => {
      addForLongident(Some((Shared.makeFlexible(val_type), Value)), path, txt, loc);
    }
    | Texp_record({fields}) => {
      addForRecord(
        expression.exp_type,
        fields |. Array.to_list |. Belt.List.keepMap(((desc, item)) => {
          switch item {
            | Overridden(loc, _) => Some((loc, desc, ()))
            | _ => None
          }
        })
      );
    }
    | Texp_constant(constant) => {
      addLocation(expression.exp_loc, Loc.Constant(constant));
    }
    /* Skip unit and list literals */
    | Texp_construct({txt: Lident("()" | "::"), loc}, _, _args) when loc.loc_end.pos_cnum - loc.loc_start.pos_cnum != 2 =>
      ()
    | Texp_construct(lident, constructor, _args) => {
      addForConstructor(expression.exp_type, lident, constructor);
    }
    | Texp_field(inner, lident, label_description) => {
      addForField(inner.exp_type, label_description, lident)
    }
    | Texp_let(_, _, _) => {
      addScopeExtent(expression.exp_loc)
      /* TODO this scope tracking won't work for recursive */
    }
    | Texp_function({cases}) => {
      switch cases {
        | [{c_rhs}] => addScopeExtent(c_rhs.exp_loc)
        | _ => ()
      }
    }
    | _ => ()
    };
    if (Collector.allLocations) {
      addLocation(expression.exp_loc, Loc.Typed(Shared.makeFlexible(expression.exp_type), Loc.NotFound));
    };
  };

  let leave_expression = expression => {
    switch (expression.exp_desc) {
    | Texp_let(_isrec, _bindings, _expr) => {
      popScopeExtent();
    }
    | Texp_function({cases}) => {
      switch cases {
        | [_] => popScopeExtent()
        | _ => ()
      }
    }
    | _ => ()
    };
    resetEnv();
  };
};

let forFile = (~file) => {
  let extra = initExtra();
  let addLocation = (loc, ident) => extra.locations = [(loc, ident), ...extra.locations];
  let addReference = (stamp, loc) => Hashtbl.replace(extra.internalReferences, stamp, [loc, ...Hashtbl.mem(extra.internalReferences, stamp) ? Hashtbl.find(extra.internalReferences, stamp) : []]);
  file.stamps.modules |> Hashtbl.iter((stamp, d: declared(Module.kind)) => {
    addLocation(d.name.loc, Loc.Module(Loc.Definition(stamp, Module)));
    addReference(stamp, d.name.loc);
  });
  file.stamps.moduleTypes |> Hashtbl.iter((stamp, d: declared(Module.kind)) => {
    addLocation(d.name.loc, Loc.Module(Loc.Definition(stamp, ModuleType)));
    addReference(stamp, d.name.loc);
  });
  file.stamps.values |> Hashtbl.iter((stamp, d: declared(Value.t)) => {
    addLocation(d.name.loc, Loc.Typed(d.contents.Value.typ, Loc.Definition(stamp, Value)));
    addReference(stamp, d.name.loc);
  });
  file.stamps.types |> Hashtbl.iter((stamp, d: declared(Type.t)) => {
    addLocation(d.name.loc, Loc.TypeDefinition(d.name.txt, d.contents.Type.typ, stamp));
    addReference(stamp, d.name.loc);
    switch (d.contents.Type.kind) {
      | Record(labels) => labels |> List.iter(({Type.Attribute.stamp, name, typ}) => {
        addReference(stamp, name.loc);
        addLocation(name.loc, Loc.Typed(typ, Loc.Definition(d.stamp, Attribute(name.txt))))
      });
      | Variant(constructos) => constructos |> List.iter(({Type.Constructor.stamp, name}) => {
        addReference(stamp, name.loc);
        let t = {
          Types.id: 0,
          level: 0,
          desc: Tconstr(Path.Pident({Ident.stamp, name: d.name.txt, flags: 0}), [], ref(Types.Mnil))
         };
        addLocation(name.loc, Loc.Typed(Shared.makeFlexible(t), Loc.Definition(d.stamp, Constructor(name.txt))))
      });
      | _ => ()
    };
  });

  extra;
};

let forItems = (~file, ~allLocations, ~processDoc, items, envs, parts) => {
  let extra = forFile(~file);

  let extent = ProcessCmt.itemsExtentNoEnv(items);
  let extent = {...extent, loc_end: {
    ...extent.loc_end,
    pos_lnum: extent.loc_end.pos_lnum + 1000000,
    pos_cnum: extent.loc_end.pos_cnum + 100000000,
  }};

  /* TODO look through parts and extend the extent */

  module Collector = {
    let filepath = Utils.parseUri(file.uri) |> Option.get;


    let scopeExtent = ref([extent]);

    let envs = ref(envs);

    let extra = extra;
    let file = file;
    let allLocations = allLocations;

    let processDoc = processDoc;
  };

  let module Iter = TypedtreeIter.MakeIterator(F(Collector));

  List.iter(Iter.iter_structure_item, items);
  /* Log.log("Parts " ++ string_of_int(Array.length(parts))); */

  parts |. Belt.Array.forEach(part => switch part {
  | Cmt_format.Partial_signature(str) =>
    Iter.iter_signature(str);
  | Partial_signature_item(str) =>
    Iter.iter_signature_item(str);
  | Partial_expression(expression) =>
    Iter.iter_expression(expression);
  | Partial_pattern(pattern) =>
    Iter.iter_pattern(pattern);
  | Partial_class_expr(class_expr) =>
    Iter.iter_class_expr(class_expr);
  | Partial_module_type(module_type) =>
    Iter.iter_module_type(module_type);
  | _ => ()
  });

  extra
};

open RResult;
let forCmt = (~file, ~allLocations, ~processDoc, {cmt_annots}: Cmt_format.cmt_infos) => switch cmt_annots {
| Partial_implementation(parts) => {
  let partsList = parts |. Array.to_list;

  let envs =  partsList |> List.rev |> List.concat_map(part => switch part {
    | Cmt_format.Partial_structure(str) => [str.str_final_env]
    | Partial_structure_item(str) => [str.str_env]
    | Partial_expression(exp) => [exp.exp_env]
    | Partial_pattern(pat) => [pat.pat_env]
    | Partial_class_expr(ce) => [ce.cl_env]
    | Partial_module_type(mty) => [mty.mty_env]
    | Partial_signature(sig_) => [sig_.sig_final_env]
    | Partial_signature_item(sig_) => [sig_.sig_env]
  });

  let items = partsList |. Belt.List.keepMap(p => switch p {
    | Partial_structure(str) => Some(str.str_items)
    | Partial_structure_item(str) => Some([str])
    /* | Partial_expression(exp) => Some([ str]) */
    | _ => None
  }) |> List.concat;
  Ok(forItems(~file, ~allLocations, ~processDoc, items, envs, parts))
}
| Implementation(structure) => {
  Ok(forItems(~file, ~allLocations, ~processDoc, structure.str_items, [structure.str_final_env], [||]))
}
| Partial_interface(pt) => {
    let envs =  pt |> Array.to_list |> List.rev |> List.concat_map(part => switch part {
      | Cmt_format.Partial_structure(str) => [str.str_final_env]
      | Partial_structure_item(str) => [str.str_env]
      | Partial_expression(exp) => [exp.exp_env]
      | Partial_pattern(pat) => [pat.pat_env]
      | Partial_class_expr(ce) => [ce.cl_env]
      | Partial_module_type(mty) => [mty.mty_env]
      | Partial_signature(sig_) => [sig_.sig_final_env]
      | Partial_signature_item(sig_) => [sig_.sig_env]
    });

    Ok(forItems(~file, ~allLocations, ~processDoc, [], envs, [||]))
  }
| Interface(sig_) => {
  /** TODO actually process signature items */
  Ok(forItems(~file, ~allLocations, ~processDoc, [], [sig_.sig_final_env], [||]))
}
| _ => Error("Invalid cmt file")
};
