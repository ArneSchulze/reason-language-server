open Compiler_libs_406;
open EnvUtils;

let classifyContext: string => option(context) = str => 
  switch str {
    | "module" => Some(`Module)
    | "module-type"
    | "modtype" => Some(`ModuleType)
    | "value"
    | "val" => Some(`Value)
    | "type" => Some(`Type)
    | "constructor"
    | "const" => Some(`Const)
    | "extension"
    | "extension-decl" => Some(`Const) // Is this correct?
    | "class" => Some(`Class)
    | "class-type"
    | "classtype" => Some(`Class)
    | "exception"
    | "exn" => Some(`Value)
    | "field"
    | "recfield" => Some(`Field)
    | "method" => Some(`Method)
    | _ => None
  }

let parseReferencePath = str => {
  let parts = str |> String.split_on_char('.');

  let parsePathComponent = str => {
    let parts = str |> String.split_on_char('-');
    switch (parts) {
      | [localContext, name] when name |> String.length >= 1 => 
        let context = classifyContext(localContext);
        Some((context, name));
      | [name] when name |> String.length >= 1 => Some((None, name))
      | _ => None
    }
  };

  let rec parsePathComponents = (parts, acc) =>
    switch parts {
      | [] => Some(List.rev(acc))
      | [first, ...rest] => 
        switch (parsePathComponent(first)) {
          | Some(component) => parsePathComponents(rest, [component, ...acc])
          | None => None
        }
    };

  parsePathComponents(parts, [])
}

let rec simplifyReferencePath = (l, accpath, accctx) =>
  switch (l) {
    | [] => (accpath, accctx)
    | [(Some(ctx), name), ...rest] =>
      let accpath = 
        switch (accpath) {
          | None => Longident.Lident(name)
          | Some(p) => Longident.Ldot(p, name)
        }
      simplifyReferencePath(rest, Some(accpath), Some(ctx))
    | [(None, name), ...rest] => 
      let accpath = 
        switch (accpath) {
          | None => Longident.Lident(name)
          | Some(p) => Longident.Ldot(p, name)
        }
      simplifyReferencePath(rest, Some(accpath), accctx)
  };

let parseReference = str => {
  let parts = str |> String.split_on_char(':');

  let maybeParsed =
    switch (parts) {
      | [globalContext, rest] => 
        let context = classifyContext(globalContext);

        switch (parseReferencePath(rest)) {
          | Some(path) => Some((context, path))
          | None => None
        }

      | [rest] => 
        switch (parseReferencePath(rest)) {
          | Some(path) => Some((None, path))
          | None => None
        }

      | _ => None
    }

  switch (maybeParsed) {
    | Some((globalContext, path)) =>
      let (path, lastContext) = simplifyReferencePath(path, None, None);

      let%opt path = path;

      let context = 
        switch (globalContext, lastContext) {
          | (Some(ctx), _) => Some(ctx)
          | (None, Some(ctx)) => Some(ctx)
          | (None, None) => None
        };

      switch (context) {
        | Some(#envContext as ctx) =>         
          Some({envContext: Some(ctx), envPath: Some(path), additionalLookup: None})
        | Some(#additionalContext as ctx) =>
          switch (path) {
            | Longident.Ldot(p, name) => 
              Some({envContext: None, envPath: Some(p), additionalLookup: Some({context: ctx, name: name})})
            | Longident.Lident(ident) => Some({envContext: None, envPath: None, additionalLookup: Some({context: ctx, name: ident})})
            | _ => None
          };
        | None => Some({envContext: None, envPath: Some(path), additionalLookup: None})
      }
    
    | None => None;
  }
}