
open Compiler_libs_406;
open Typedtree;
open SharedTypes;
open Infix;
open Unix;
open EnvUtils;
open OdocUtils;

let getTopDoc = structure => {
  switch structure {
  | [(_envs, {str_desc: Tstr_attribute(
      ({Asttypes.txt: "ocaml.doc" | "ocaml.text"}, PStr([{pstr_desc: Pstr_eval({pexp_desc: Pexp_constant(
    Pconst_string
    (doc, _))}, _)}])))}), ...rest] =>
    (Some(doc), rest)
  | _ => (None, structure)
  };
};

let getTopSigDoc = structure => {
  switch structure {
  | [{sig_desc: Tsig_attribute(
    ({Asttypes.txt: "ocaml.doc" | "ocaml.text"}, PStr([{pstr_desc: Pstr_eval({pexp_desc: Pexp_constant(
    Pconst_string
    (doc, _))}, _)}])))}, ...rest] =>
    (Some(doc), rest)
  | _ => (None, structure)
  };
};

let itemsExtent = items => {
  open Typedtree;
  items == [] ? Location.none : {
    let (_envs, first) = List.hd(items);
    let (_envs, last) = List.nth(items, List.length(items) - 1);
    let (first, last) = first.str_loc.loc_start.pos_cnum <
      last.str_loc.loc_start.pos_cnum ? (first, last) : (last, first);

    {
      loc_ghost: true,
      loc_start: first.str_loc.loc_start,
      loc_end: last.str_loc.loc_end,
    };
  };
};


let structItemsExtent = items => {
  open Typedtree;
  items == [] ? Location.none : {
    let (_envs, first) = List.hd(items);
    let (_envs, last) = List.nth(items, List.length(items) - 1);
    let (first, last) = first.str_loc.loc_start.pos_cnum <
      last.str_loc.loc_start.pos_cnum ? (first, last) : (last, first);

    {
      loc_ghost: true,
      loc_start: first.str_loc.loc_start,
      loc_end: last.str_loc.loc_end,
    };
  };
};

let sigItemsExtend = items => {
  open Typedtree;
  items == [] ? Location.none : {
    let (_envs, first) = List.hd(items);
    let (_envs, last) = List.nth(items, List.length(items) - 1);
    let (first, last) = first.sig_loc.loc_start.pos_cnum <
      last.sig_loc.loc_start.pos_cnum ? (first, last) : (last, first);

    {
      loc_ghost: true,
      loc_start: first.sig_loc.loc_start,
      loc_end: last.sig_loc.loc_end,
    };
  };
};

let itemsExtentNoEnv = items => {
  open Typedtree;
  items == [] ? Location.none : {
    let first = List.hd(items);
    let last = List.nth(items, List.length(items) - 1);
    let (first, last) = first.str_loc.loc_start.pos_cnum <
      last.str_loc.loc_start.pos_cnum ? (first, last) : (last, first);

    {
      loc_ghost: true,
      loc_start: first.str_loc.loc_start,
      loc_end: last.str_loc.loc_end,
    };
  };
}

let sigItemsExtent = items => {
  open Typedtree;
  items == [] ? Location.none : {
    let first = List.hd(items);
    let last = List.nth(items, List.length(items) - 1);

    {
      Location.loc_ghost: true,
      loc_start: first.sig_loc.loc_start,
      loc_end: last.sig_loc.loc_end,
    };
  };
};

let locStartPos = ({Location.loc_start: {pos_cnum, pos_lnum, pos_bol}}) => (
  pos_lnum,
  pos_cnum - pos_bol
);

type env = {
  stamps,
  processDoc: (~location: Compiler_libs_406.Location.t, ~resolveLink: string => (option(string), string), string) => string,
  modulePath: visibilityPath,
  scope: Location.t,
  modname: string
};

let newDeclared = ProcessAttributes.newDeclared;

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
  

let resolveWithEnvs = (filename, modname, envs, unparsed) => {
  switch (parseReference(unparsed)) {
    | None => (None, unparsed)
    | Some(lookupPath) => 
      let res = findInEnvs(envs, lookupPath) |?>> locToUri(filename);
      
      let res =
        switch (res) {
          | None => 
            let lookupPath = {
              ...lookupPath,
              envPath: switch (lookupPath.envPath) {
                | Some(l) => Some(wind_lident([modname, ...unwind_lident(l, [])], None))
                | None => Some(Longident.Lident(modname))
              }
            }
            findInEnvs(envs, lookupPath) |?>> locToUri(filename);
          | Some(_) as res => res
        };

      (res, lookupPath.envPath->Belt.Option.mapWithDefault(lookupPath.additionalLookup->Belt.Option.mapWithDefault(unparsed, add => add.name), p => {
        let p = lident_to_string(p);
        lookupPath.additionalLookup->Belt.Option.mapWithDefault(p, add => p ++ "." ++ add.name)
      }));
  }
}

let addItem = (~file, ~name, ~extent, ~stamp, ~env, ~contents, ~envs, attributes, exported, stamps) => {
  let declared = newDeclared(
    ~contents,
    ~scope={
      Location.loc_start: extent.Location.loc_end,
      loc_end: env.scope.loc_end,
      loc_ghost: false,
    },
    ~extent,
    ~name,
    ~stamp,
    ~modulePath=env.modulePath,
    ~processDoc=env.processDoc(~resolveLink=resolveWithEnvs(file, env.modname, envs)),
    ! Hashtbl.mem(exported, name.txt),
    attributes,
  );
  if (!Hashtbl.mem(exported, name.txt)) {
    Hashtbl.add(exported, name.txt, stamp);
  };
  Hashtbl.add(stamps, stamp, declared);
  declared;
};

let addItemAnonymous = (~file, ~extent, ~loc, ~stamp, ~env, ~contents, ~envs, attributes, exported, stamps) => {
  let declared = newDeclared(
    ~contents,
    ~scope={
      Location.loc_start: extent.Location.loc_end,
      loc_end: env.scope.loc_end,
      loc_ghost: false,
    },
    ~extent,
    ~name={txt: "", loc},
    ~stamp,
    ~modulePath=env.modulePath,
    ~processDoc=env.processDoc(~resolveLink=resolveWithEnvs(file, env.modname, envs)),
    false,
    attributes,
  );
  Hashtbl.add(stamps, stamp, declared);
  declared;
};

let getModuleTypePath = (mod_desc) => switch mod_desc {
  | Tmty_ident(path, _)
  | Tmty_alias(path, _) => Some(path)
  | Tmty_signature(_)
  | Tmty_functor(_)
  | Tmty_with(_)
  | Tmty_typeof(_) => None
};

let forTypeDeclaration = (~file, ~env, ~envs, ~exported: Module.exported, {typ_id, typ_loc, typ_params, typ_name: name, typ_attributes, typ_type, typ_kind, typ_manifest}) => {
  let stamp = Ident.binding_time(typ_id);
  let declared = addItem(~file, ~extent=typ_loc, ~contents={
    Type.params: typ_params |> List.map(((t, _)) => (Shared.makeFlexible(t.ctyp_type), t.ctyp_loc)),
    typ: Shared.makeDeclaration(typ_type),
    kind: switch typ_kind {
      | Ttype_abstract =>
        switch (typ_manifest) {
          | Some({ctyp_desc: Ttyp_constr(path, _lident, args)}) => Abstract(Some((
            (path),
            args |> List.map(t => Shared.makeFlexible(t.ctyp_type))
          )))
          | Some({ctyp_desc: Ttyp_tuple(items)}) => Tuple(items |> List.map(t => Shared.makeFlexible(t.ctyp_type)))
          /* TODO dig */
          | _ => Abstract(None)
        }
      | Ttype_open => Open
      | Ttype_variant(constructors) => Variant(constructors |> List.map(({cd_id, cd_name: name, cd_args, cd_res}) => {
        let stamp = Ident.binding_time(cd_id);
      {
        Type.Constructor.stamp,
        name,
        args: switch (cd_args) {
          | Cstr_tuple(args) => args
        /* TODO(406) */
          | Cstr_record(_) => []
        } |>
          List.map(t => (Shared.makeFlexible(t.ctyp_type), t.ctyp_loc)),
        res: cd_res |?>> t => Shared.makeFlexible(t.ctyp_type),
      }}))
      | Ttype_record(labels) => Record(labels |> List.map(
        ({ld_id, ld_name: name, ld_type: {ctyp_type, ctyp_loc}}) => {
        let astamp = Ident.binding_time(ld_id);
          {Type.Attribute.stamp: astamp, name, typ: Shared.makeFlexible(ctyp_type), typLoc: ctyp_loc}
        }))
    }
  }, ~name, ~stamp, ~env,
      ~envs, typ_attributes, exported.types, env.stamps.types);
  {...declared, contents: Module.Type(declared.contents)}
};


let rec getModulePath = (mod_desc) => switch mod_desc {
  | Tmod_ident(path, _lident) => Some(path)
  | Tmod_structure(_) => None
  | Tmod_functor(_ident, _argName, _maybeType, _resultExpr) => None
  | Tmod_apply(functor_, _arg, _coercion) => getModulePath(functor_.mod_desc)
  | Tmod_unpack(_expr, _moduleType) => None
  | Tmod_constraint(expr, _typ, _constraint, _coercion) => getModulePath(expr.mod_desc)
};

let rec forItem = (
  ~file,
  ~env,
  ~exported: Module.exported,
  envs,
  item
) => {
  let envs = [item.str_env, ...envs];
  switch (item.str_desc) {
    | Tstr_value(_isRec, bindings) =>
      optMap(({vb_loc, vb_pat: {pat_desc, pat_type}, vb_attributes,}) =>
        /* TODO get all the things out of the var. */
        switch (pat_desc) {
          | Tpat_var(ident, name) =>
            let contents = {
              Value.recursive: false,
              typ: Shared.makeFlexible(pat_type),
            };
            let declared = addItem(~file, ~name, ~stamp=Ident.binding_time(ident), ~env, ~envs, ~extent=vb_loc, ~contents, vb_attributes, exported.values, env.stamps.values);
            Some({...declared, contents: Module.Value(declared.contents)})
          | _ => None
        },
      bindings)
    | Tstr_module({mb_id, mb_attributes, mb_loc, mb_name: name, mb_expr: {mod_desc, mod_env}}) => {
      let contents = forModule(~file, env, [mod_env, ...envs], mod_desc, name.txt);
      let declared = addItem(~file, ~contents, ~name, ~extent=mb_loc, ~stamp=Ident.binding_time(mb_id), ~env, ~envs, mb_attributes, exported.modules, env.stamps.modules);
      [{...declared, contents: Module.Module(declared.contents)}]
    }
    | Tstr_recmodule(mod_list) => mod_list |> List.concat_map(({mb_id, mb_attributes, mb_loc, mb_name: name, mb_expr: {mod_desc, mod_env}}) => {
        let contents = forModule(~file,env, [mod_env, ...envs], mod_desc, name.txt);
        let declared = addItem(~file, ~contents, ~name, ~extent=mb_loc, ~stamp=Ident.binding_time(mb_id), ~env, ~envs, mb_attributes, exported.modules, env.stamps.modules);
        [{...declared, contents: Module.Module(declared.contents)}]
      })
    | Tstr_modtype({mtd_type: Some(moduleType), mtd_loc, mtd_name: name, mtd_id, mtd_attributes}) => {
        let contents = forModuleType(~file,env, [moduleType.mty_env, ...envs], moduleType.mty_desc, name.txt)
        let declared = addItem(~file, ~contents, ~name, ~extent=mtd_loc, ~stamp=Ident.binding_time(mtd_id), ~env, ~envs=[moduleType.mty_env, ...envs], List.concat([mtd_attributes, moduleType.mty_attributes]), exported.moduleTypes, env.stamps.moduleTypes);
        [{...declared, contents: Module.ModuleType(declared.contents)}]
      }
    | Tstr_include({incl_mod, incl_type}) =>
      let env = switch (getModulePath(incl_mod.mod_desc)) {
        | None => env
        | Some(path) => {
          ...env,
          modulePath: IncludedModule((path), env.modulePath)
        }
      };
      let topLevel = List.fold_right((item, items) => {
        forSignatureTypeItem(~file, env, envs, exported, item) @ items
      }, incl_type, []) |> List.rev;

      topLevel

    | Tstr_primitive({val_id, val_name: name, val_loc, val_attributes, val_val: {val_type}}) => {
      let declared = addItem(~file, ~extent=val_loc, ~contents={Value.recursive: false, typ: Shared.makeFlexible(val_type)}, ~name, ~stamp=Ident.binding_time(val_id), ~env, ~envs, val_attributes, exported.values, env.stamps.values);
      [{...declared, contents: Module.Value(declared.contents)}]
    }
    | Tstr_type(_, decls) =>
      decls |> List.map(forTypeDeclaration(~file, ~env, ~envs, ~exported))
    | _ => []
  }
}

and forSignatureTypeItem = (~file, env, envs, exported: SharedTypes.Module.exported, item) => {
  open Types;
  switch item {
  | Sig_value(ident, {val_type, val_attributes, val_loc: loc}
  ) => {
    let contents = {
      Value.recursive: false,
      typ: Shared.makeFlexible(val_type),
    };
    let declared = addItem(
      ~file,
      ~name=Location.mknoloc(Ident.name(ident)),
      ~extent=loc,
      ~stamp=Ident.binding_time(ident),
      ~env,
      ~contents,
      ~envs,
      val_attributes,
      exported.values,
      env.stamps.values,
    );
    [{...declared, contents: Module.Value(declared.contents)}]
  }
  | Sig_type(
    ident,
    {type_params, type_loc, type_kind, type_manifest, type_attributes} as decl,
    _
    ) => {
    let declared = addItem(~file, ~extent=type_loc, ~contents={
      Type.params: type_params |> List.map(t => (Shared.makeFlexible(t), Location.none)),
      typ: Shared.makeDeclaration(decl),
      kind: switch type_kind {
        | Type_abstract =>
        switch (type_manifest) {
          | Some({desc: Tconstr(path, args, _)}) => Abstract(Some((
              path,
            args |> List.map(Shared.makeFlexible)
          )))
          | Some({desc: Ttuple(items)}) => Tuple(items |> List.map(Shared.makeFlexible))
          /* TODO dig */
          | _ => Abstract(None)
        }
        | Type_open => Open
        | Type_variant(constructors) => {
          Variant(constructors |. Belt.List.map(({cd_loc, cd_id, cd_args, cd_res, cd_attributes}) => {
            let name = Ident.name(cd_id);
            let stamp = Ident.binding_time(cd_id);
            let contents = {
              Type.Constructor.stamp,
              name: Location.mknoloc(name),
              args: switch (cd_args) {
                | Cstr_tuple(args) => args
              /* TODO(406): constructor record args support */
                | Cstr_record(_) => []
              } |>
                List.map(t => (Shared.makeFlexible(t), Location.none)),
              res: cd_res |?>> Shared.makeFlexible,
            };
            let declared = newDeclared(
              ~contents,
              ~extent=cd_loc,
              ~scope={
                Location.loc_start: type_loc.Location.loc_end,
                loc_end: env.scope.loc_end,
                loc_ghost: false,
              },
              ~name=Location.mknoloc(name),
              ~stamp,
              /* TODO maybe this needs another child */
              ~modulePath=env.modulePath,
              ~processDoc=env.processDoc(~resolveLink=resolveWithEnvs(file, env.modname, envs)),
              true,
              cd_attributes,
            );
            Hashtbl.add(env.stamps.constructors, stamp, declared);
            contents
          }))
        }
        | Type_record(labels, _) => Record(labels |> List.map(
          ({ld_id, ld_type}) => {
            let astamp = Ident.binding_time(ld_id);
            let name = Ident.name(ld_id);
            {Type.Attribute.stamp: astamp, name: Location.mknoloc(name), typ: Shared.makeFlexible(ld_type), typLoc: Location.none}
          }
        ))
      }
    }, ~name=Location.mknoloc(Ident.name(ident)), ~stamp=Ident.binding_time(ident), ~env,
      ~envs, type_attributes, exported.types, env.stamps.types);
    [{...declared, contents: Module.Type(declared.contents)}]
  }
  /* | Sig_module({stamp, name}, {md_type: Mty_ident(path) | Mty_alias(path), md_attributes, md_loc}, _) =>
    let declared = addItem(~contents=Module.Ident(path), ~name=Location.mknoloc(name), ~stamp, ~env, md_attributes, exported.modules, env.stamps.modules);
    [{...declared, contents: Module.Module(declared.contents)}, ...items] */
  | Sig_module(
    ident,
    {md_type, md_attributes, md_loc},
    _
  ) =>
    let declared = addItem(
      ~file,
      ~extent=md_loc,
      ~contents=forModuleTypeType(~file, env, envs, md_type),
      ~name=Location.mknoloc(Ident.name(ident)),
      ~stamp=Ident.binding_time(ident),
      ~env,
      ~envs,
      md_attributes,
      exported.modules,
      env.stamps.modules);
    [{...declared, contents: Module.Module(declared.contents)}]
  | _ => []
  }
}

and forSignature = (~file, ~env, ~envs, items) => {
  let (doc, items) = getTopSigDoc(items);
  let exported = Module.initExported();
  let topLevel = Belt.List.map(items, forSignatureItem(~file, ~env, ~envs, ~exported)) |> Belt.List.flatten;
  (doc, {Module.exported, topLevel})
}

and forSignatureItem = (~file, ~env, ~envs, ~exported: Module.exported, item) => {
  let envs = [item.sig_env, ...envs];
  switch (item.sig_desc) {
  | Tsig_value({val_id, val_loc, val_name: name, val_desc, val_attributes}) => {
    let declared = addItem(
      ~file,
      ~name,
      ~stamp=Ident.binding_time(val_id),
      ~extent=val_loc,
      ~contents={Value.typ: Shared.makeFlexible(val_desc.ctyp_type), recursive: false},
      ~env,
      ~envs,
      val_attributes,
      exported.values,
      env.stamps.values
    );
    [{...declared, contents: Module.Value(declared.contents)}]
  }
  | Tsig_type(_/*402*/, decls) => {
    decls |> List.map(forTypeDeclaration(~file, ~env, ~envs, ~exported))
  }
  | Tsig_module({md_id, md_attributes, md_loc, md_name: name, md_type: {mty_desc, mty_env}}) => {
    let contents = forModuleType(~file, env, [mty_env, ...envs], mty_desc, name.txt);
    let declared = addItem(~file, ~contents, ~name, ~extent=md_loc, ~stamp=Ident.binding_time(md_id), ~env,
      ~envs, md_attributes, exported.modules, env.stamps.modules);
    [{...declared, contents: Module.Module(declared.contents)}]
  }
  | Tsig_recmodule(mod_list) => mod_list |> List.concat_map(({md_id, md_attributes, md_loc, md_name: name, md_type: {mty_desc, mty_env}}) => {
      let contents = forModuleType(~file, env, [mty_env, ...envs], mty_desc, name.txt);
      let declared = addItem(~file, ~contents, ~name, ~extent=md_loc, ~stamp=Ident.binding_time(md_id), ~env,
        ~envs, md_attributes, exported.modules, env.stamps.modules);
      [{...declared, contents: Module.Module(declared.contents)}]
    })
  | Tsig_modtype({mtd_type: Some(moduleType), mtd_loc, mtd_name: name, mtd_id, mtd_attributes}) => {
      let contents = forModuleType(~file, env, [moduleType.mty_env, ...envs], moduleType.mty_desc, name.txt)
      let declared = addItem(~file, ~contents, ~name, ~extent=mtd_loc, ~stamp=Ident.binding_time(mtd_id), ~env, ~envs=[moduleType.mty_env, ...envs], List.concat([mtd_attributes, moduleType.mty_attributes]), exported.moduleTypes, env.stamps.moduleTypes);
      [{...declared, contents: Module.ModuleType(declared.contents)}]
    }
  | Tsig_include({incl_mod, incl_loc, incl_type}) =>
    let env = switch (getModuleTypePath(incl_mod.mty_desc)) {
      | None => env
      | Some(path) => {
        ...env,
        modulePath: IncludedModule((path), env.modulePath)
      }
    };


    let contents = forModuleType(~file, env, [incl_mod.mty_env, ...envs], incl_mod.mty_desc, "");
    
    switch (contents) {
      | Module.Ident(_) => List.fold_right((item, items) => {
          forSignatureTypeItem(~file, env, envs, exported, item) @ items
        }, incl_type, []) |> List.rev
      | Module.Structure(contents) => contents.topLevel
    }
  /* TODO: process other things here */
  | _ => []
  }
}

and forSignatureType = (~file, env, envs, signature) => {
  let exported = Module.initExported();
  let topLevel = List.fold_right((item, items) => {
    forSignatureTypeItem(~file, env, envs, exported, item) @ items
  }, signature, []) |> List.rev;

  {Module.exported, topLevel}
} 

and forModuleType = (~file, env, envs: list(Env.t), moduleType, moduleName: string) => switch moduleType {
  | Tmty_ident(path, _ident) => Module.Ident((path))
  | Tmty_alias(path, _ident) => Module.Ident((path))
  | Tmty_signature(signature) => 
    let env = {...env, scope: sigItemsExtent(signature.sig_items), modulePath: ExportedModule(moduleName, env.modulePath)};
    let (_docs, contents) = forSignature(~file, ~env, ~envs=[signature.sig_final_env, ...envs], signature.sig_items);
    Module.Structure(contents)
  | Tmty_functor(_argIdent, _arg, _argType, resultType) => forModuleType(~file, env, envs, resultType.mty_desc, moduleName)
  | Tmty_with(moduleType, _withs) => forModuleType(~file, env, envs, moduleType.mty_desc, moduleName)
  | Tmty_typeof({mod_desc, mod_env}) => forModule(~file, env, [mod_env, ...envs], mod_desc, moduleName)
}

and forModuleTypeType = (~file, env, envs: list(Env.t), moduleType) => switch moduleType {
  | Types.Mty_ident(path) => Module.Ident((path))
  | Mty_alias(_, path) => Module.Ident((path))
  | Mty_signature(signature) => 
    Module.Structure(forSignatureType(~file, env, envs, signature))
  | Mty_functor(_ident, _argType, resultType) => forModuleTypeType(~file, env, envs, resultType)
}

and forModule = (~file, env, envs, mod_desc, moduleName) => switch mod_desc {
  | Tmod_ident(path, _lident) => Module.Ident((path))
  | Tmod_structure(structure) => {
    let items = structure.str_items |> List.map(str_item => ([structure.str_final_env, ...envs], str_item));
    let env = {...env, scope: structItemsExtent(items), modulePath: ExportedModule(moduleName, env.modulePath)};
    let (_doc, contents) = forStructure(~file, ~env, items);
    Module.Structure(contents)
  }
  | Tmod_functor(ident, argName, maybeType, resultExpr) => {
    maybeType |?< t => {
      let kind = forModuleType(~file, env, envs, t.mty_desc, argName.txt);
      let stamp = Ident.binding_time(ident);
      let declared = newDeclared(
        ~contents=kind,
        ~name=argName,
        ~scope={
          Location.loc_start: t.mty_loc.loc_end,
          loc_end: env.scope.loc_end,
          loc_ghost: false,
        },
        ~extent=t.Typedtree.mty_loc,
        ~stamp,
        ~modulePath=NotVisible,
        ~processDoc=env.processDoc(~resolveLink=resolveWithEnvs(file, env.modname, envs)),
        false,
        [],
      );
      Hashtbl.add(env.stamps.modules, stamp, declared);
    };
    forModule(~file, env, [resultExpr.mod_env, ...envs], resultExpr.mod_desc, moduleName)
  }
  | Tmod_apply(functor_, _arg, _coercion) => forModule(~file, env, [functor_.mod_env, ...envs], functor_.mod_desc, moduleName)
  | Tmod_unpack(_expr, moduleType) =>
    let env = {...env, modulePath: ExportedModule(moduleName, env.modulePath)};
    forModuleTypeType(~file, env, envs, moduleType)
  | Tmod_constraint(expr, typ, _constraint, _coercion) => {
    /* TODO do this better I think */
    let env = {...env, modulePath: ExportedModule(moduleName, env.modulePath)};
    forModuleTypeType(~file, env, [expr.mod_env, ...envs], typ)
  }
}

and forStructure = (~file, ~env, items: list((list(Env.t), Typedtree.structure_item))) => {
  let (doc, items) = getTopDoc(items);
  let exported = Module.initExported();
  let topLevel = List.fold_right(((envs, item), results) => {
    forItem(~file, ~env, ~exported, envs, item) @ results
  }, items, []);
  (doc, {Module.exported, topLevel})
};

let rec getAllToplevelEnvs = (arr: array(Cmt_format.binary_part), idx, acc) => 
  if (idx >= Array.length(arr)) {
    acc |> List.rev |> List.concat;
  } else {
    let str_items_with_env = 
      switch (arr[idx]) {
        | Partial_structure(str) =>
          str.str_items |> List.map(str_item => ([str.str_final_env], str_item))
        | Partial_structure_item(str) =>
          [([], str)]
        | Partial_expression(expr) =>
          [([], {str_desc: Tstr_eval(expr, []), str_loc: expr.exp_loc, str_env: expr.exp_env})]
        | _ => []
      }

    getAllToplevelEnvs(arr, idx + 1, [str_items_with_env, ...acc]);
  };

let print_binary_part = (f, part) => {
  switch (part) {
  | Cmt_format.Partial_structure(str) => Printtyped.implementation(f, str);
  | Partial_structure_item(str_item) => Printtyped.structure_item(f, str_item);
  | Partial_signature(sign) => Printtyped.interface(f, sign);
  | Partial_signature_item(sig_item) => Printtyped.signature_item(f, sig_item);
  | _ => Format.pp_print_string(f, "Unknown");
  };
  Format.pp_print_newline(f, ());  
}

let _print_binary_annots = annots => {
  let f = Format.str_formatter;
  switch (annots) {
    | Cmt_format.Implementation(str) => Format.pp_print_string(f, "Implementation"); Format.pp_print_newline(f, ()); Printtyped.implementation(f, str);
    | Interface(sign) => Format.pp_print_string(f, "Interface"); Format.pp_print_newline(f, ()); Printtyped.interface(f, sign);
    | Partial_implementation(parts) =>
      Format.pp_print_string(f, "Partial Implementation"); Format.pp_print_newline(f, ());
      Array.iter(print_binary_part(f), parts);
    | Partial_interface(parts) =>
      Format.pp_print_string(f, "Partial Interface"); Format.pp_print_newline(f, ());
      Array.iter(print_binary_part(f), parts);
    | _ => Format.pp_print_string(f, "Unknown");
  }
  Format.pp_print_newline(f, ());
  Log.log(Format.flush_str_formatter() ++ "\n");
}

let fixLocation = (file, loc: Location.t) => {
  let loc_start = 
    if (loc.loc_start.pos_fname == "") {
      {...loc.loc_start, pos_fname: file};
    } else {
      loc.loc_start
    };
  let loc_end = 
    if (loc.loc_end.pos_fname == "") {
      {...loc.loc_end, pos_fname: file};
    } else {
      loc.loc_end
    };
  {...loc, loc_start, loc_end}
}

open RResult;
let forCmt = (~moduleName, uri, processDoc, {cmt_modname, cmt_annots, cmt_loadpath}: Cmt_format.cmt_infos) => {

  Config.load_path := cmt_loadpath;
  let file = Utils.parseUri(uri) |> Option.get;

  let processDoc = (~location) => processDoc(~location=fixLocation(file, location));

  switch cmt_annots {
  | Partial_implementation(parts) => {
    let items = getAllToplevelEnvs(parts, 0, []);
    let extent = structItemsExtent(items);
    let extent = {...extent, loc_end: {
      ...extent.loc_end,
      pos_lnum: extent.loc_end.pos_lnum + 1000000,
      pos_cnum: extent.loc_end.pos_cnum + 100000000,
    }};
    let env = {
      scope: extent,
      stamps: initStamps(),
      processDoc,
      modulePath: File(uri, moduleName),
      modname: cmt_modname
    };
    let (docstring, contents) = forStructure(~file,~env, items);
    Ok({uri, moduleName: cmt_modname, stamps: env.stamps, docstring, contents})
  }
  | Partial_interface(parts) => {
    let items = parts |. Array.to_list |. Belt.List.keepMap(p => switch p {
      | Partial_signature(str) => Some(str.sig_items)
      | Partial_signature_item(str) => Some([str])
      | _ => None
    }) |> List.concat;
    let envs = parts |. Array.to_list |. Belt.List.keepMap(p => switch p {
      | Partial_signature(str) => Some(str.sig_final_env)
      | Partial_signature_item(str) => Some(str.sig_env)
      | _ => None
    }) |> List.rev;
    let env = {scope: sigItemsExtent(items), stamps: initStamps(), processDoc, modulePath: File(uri, moduleName), modname: cmt_modname};
    let (docstring, contents) = forSignature(~file, ~env, ~envs, items);
    Ok({uri, moduleName: cmt_modname, stamps: env.stamps, docstring, contents})
  }
  | Implementation(structure) => {
    let items = structure.str_items |> List.map(str_item => ([structure.str_final_env], str_item));
    let env = {scope: structItemsExtent(items), stamps: initStamps(), processDoc, modulePath: File(uri, moduleName), modname: cmt_modname};
    let (docstring, contents) = forStructure(~file, ~env, items);
    Ok({uri, moduleName: cmt_modname, stamps: env.stamps, docstring, contents})
  }
  | Interface(signature) => {
    let env = {scope: sigItemsExtent(signature.sig_items), stamps: initStamps(), processDoc, modulePath: File(uri, moduleName), modname: cmt_modname};
    let (docstring, contents) = forSignature(~file, ~env, ~envs=[signature.sig_final_env], signature.sig_items);
    Ok({uri, moduleName: cmt_modname, stamps: env.stamps, docstring, contents})
  }
  | _ => {
    Error("Not a valid cmt")
  }
  };
}

let forCmi = (~moduleName, uri, processDoc, {cmi_name, cmi_sign}: Cmi_format.cmi_infos) => {
  let file = Utils.parseUri(uri) |> Option.get;
  let env = {scope: Location.none, stamps: initStamps(), processDoc, modulePath: File(uri, moduleName), modname: cmi_name};
  let contents = forSignatureType(~file, env,[], cmi_sign);
  Some({
    uri,
    moduleName: cmi_name,
    stamps: env.stamps,
    docstring: Some("No docstring for cmi files"),
    contents,
  });
};
