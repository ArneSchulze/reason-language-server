open Odoc_parser;

let withStyle = (style, contents) => switch style {
| `Bold => Omd.Strong([], contents)
| `Italic => Omd.Emph([], contents)
| `Emphasis => Omd.Emph([], contents)
| `Superscript => Omd.Emph([], contents)
| `Subscript => Omd.Emph([], contents)
};

let pp_styled = (formatter, style, format, contents) =>
  switch (style) {
  | `Bold => Format.fprintf(formatter, "**%a**", format, contents)
  | `Italic
  | `Emphasis
  | `Subscript
  | `Superscript => Format.fprintf(formatter, "_%a_", format, contents)
  };

let rec find_tick_repetition = (str, char, index, chain, longest) =>
  if (index >= String.length(str)) {
    longest;
  } else {
    if (str.[index] == char) {
      find_tick_repetition(str, char, index + 1, chain + 1, longest);
    } else {
      find_tick_repetition(str, char, index + 1, 0, if (chain > longest) { chain } else { longest });
    }
  };

let find_tick_repetition = (str, char) => find_tick_repetition(str, char, 0, 0, 0);

let rec pp_inline_ele = (~resolveLink, formatter, item: Loc.with_location(Ast.inline_element)) =>
  switch item.value {
  | `Space(str) => Format.fprintf(formatter, " ")
  | `Word(text) => Format.fprintf(formatter, "%s", text)
  | `Code_span(text) => 
    let repitition = find_tick_repetition(text, '`');
    let opener = String.make(repitition + 1, '`');
    Format.fprintf(formatter, "%s%s%s", opener, text, opener)
  | `Math_span(text) => 
    let repitition = find_tick_repetition(text, '$');
    let opener = String.make(repitition + 1, '$');
    Format.fprintf(formatter, "%s%s%s", opener, text, opener) // TODO: Separate math?
  | `Link(href, content) =>
    Format.fprintf(
      formatter,
      "[%a](<%s>)",
      Format.pp_print_list(pp_inline_ele(~resolveLink)),
      content,
      href,
    )
  | `Styled(style, contents) =>
    pp_styled(formatter, style, Format.pp_print_list(pp_inline_ele(~resolveLink)), contents)
  | `Reference(kind, target, content) =>
    let (maybeLink, sanitizedTarget) = resolveLink(target.value);

    let content = 
      switch (content) {
        | [] => [{Loc.value: `Code_span(sanitizedTarget), location: item.location}]
        | e => e
      };

    switch (maybeLink) {
      | None =>
        Format.fprintf(formatter, "%a", Format.pp_print_list(pp_inline_ele(~resolveLink)), content)
      | Some(link) =>
        Format.fprintf(
          formatter,
          "[%a](<%s>)",
          Format.pp_print_list(pp_inline_ele(~resolveLink)),
          content,
          link,
        )
    }
  | `Raw_markup(_, text) => Format.fprintf(formatter, "%s", text)
  };

let pp_heading = (~resolveLink, formatter, level, content: list(Loc.with_location(Ast.inline_element))) => {
  let level = switch (level) {
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 5 => 5
    | _ => 6
    };
  Format.fprintf(
    formatter,
    "%s %a",
    String.make(level, '#'),
    Format.pp_print_list(pp_inline_ele(~resolveLink)),
    content,
  );
};

let pp_module_link = (~resolveLink, formatter, target) => {
  let (maybeLink, sanitizedTarget) = resolveLink(target.Loc.value);
  switch (maybeLink) {
    | None => Format.fprintf(formatter, "`%s`", sanitizedTarget)
    | Some(link) => Format.fprintf(formatter, "[%s](<%s>)", sanitizedTarget, link)
  }
}

let pp_quote_newline = (pp_newline, formatter, ()) => {
  Format.fprintf(formatter, "%a> ", pp_newline, ());
}

let pp_block_delimit = (pp_newline, formatter, ()) => {
  Format.fprintf(formatter, "%a%a", pp_newline, (), pp_newline, ());
}

let pp_block_list_delimit = (pp_newline, formatter, ()) => {
  Format.fprintf(formatter, "  %a", pp_newline, ());
}

let pp_newline_ident = (pp_newline, formatter, ()) => Format.fprintf(formatter, "%a    ", pp_newline, ());

let pp_list_idx = (~pp_sep=(_, _idx) => (), format, formatter, list) => {
  let rec helper = (l, idx) =>
    switch (l) {
      | [] => ()
      | [x] => Format.fprintf(formatter, "%a", format(idx), x)
      | [x, ...rest] =>
        Format.fprintf(formatter, "%a%a", format(idx), x, pp_sep, idx);
        helper(rest, idx + 1);
    };
  helper(list, 1);
}

let pp_info_box = (pp_newline, tip, format, formatter, content) => {
  let title = 
    switch tip {
      | `Note => "[!NOTE]"
      | `Tip => "[!TIP]"
      | `Important => "[!IMPORTANT]"
      | `Warning => "[!WARNING]"
      | `Caution => "[!CAUTION]"
    };
  let pp_newline = pp_quote_newline(pp_newline);
  let contentFormat = Format.pp_print_list(~pp_sep=pp_block_list_delimit(pp_newline), format(pp_newline));
  Format.fprintf(formatter, "%a%s  %a%a", pp_newline, (), title, pp_newline, (), contentFormat, content);
};

let rec pp_nestable_block_element = (~resolveLink, pp_newline, formatter, item: Loc.with_location(Ast.nestable_block_element)) =>
  switch item.value {
  | `Paragraph(inline) =>
    Format.fprintf(
      formatter,
      "%a",
      Format.pp_print_list(pp_inline_ele(~resolveLink)),
      inline,
    )
  | `Code_block({meta, content: {value}}) =>
    let lang = meta->Belt.Option.mapWithDefault("ml", meta => meta.language.value);
    Format.fprintf(formatter, "```%s%a%s%a```", lang, pp_newline, (), value, pp_newline, ())
  | `Verbatim(text) => Format.fprintf(formatter, "```%a%s%a```", pp_newline, (), text, pp_newline, ()) /* TODO */
  | `Modules(modules) =>
    let pp_sep = (formatter, _idx) => {
      Format.fprintf(formatter, "%a- ", pp_newline, ());
    }
    let pp_ele = (_idx) => pp_module_link(~resolveLink);
    let format = pp_list_idx(~pp_sep, pp_ele);
    Format.fprintf(formatter, "- %a", format, modules)
  | `List(`Ordered, _weight, children) =>
    let pp_sep = (formatter, idx) => {
      Format.fprintf(formatter, "%a%d. ", pp_newline, (), idx + 1);
    }
    let pp_ele = (_idx) => pp_block_elements_in_list(~resolveLink, pp_newline_ident(pp_newline));
    let format = pp_list_idx(~pp_sep, pp_ele);
    Format.fprintf(formatter, "1. %a", format, children :> list(list(Loc.with_location(Ast.block_element))));
  | `List(`Unordered, _weight, children) =>
    let pp_sep = (formatter, _idx) => {
      Format.fprintf(formatter, "%a- ", pp_newline, ());
    }
    let pp_ele = (_idx) => pp_block_elements_in_list(~resolveLink, pp_newline_ident(pp_newline));
    let format = pp_list_idx(~pp_sep, pp_ele);
    Format.fprintf(formatter, "- %a", format, children :> list(list(Loc.with_location(Ast.block_element))))
  | `Table(_,_)
  | `Math_block(_)
  | `Media(_) => ()
  }

and pp_tag = (~resolveLink, pp_newline, formatter, tag: Loc.with_location([ Ast.ocamldoc_tag | Ast.internal_tag])) =>
  switch tag.value {
  | `Author(string) => pp_info_box(pp_newline, `Note, (_) => pp_inline_ele(~resolveLink), formatter, [{value: `Word("Author: " ++ string), location: tag.location}])

  | `Deprecated(contents) => 
    pp_info_box(pp_newline, `Warning, pp_nestable_block_element(~resolveLink), formatter, contents)

  | `Param(name, contents) => 
    pp_info_box(pp_newline, `Note, pp_nestable_block_element(~resolveLink), formatter, contents)

  | `Raise(name, contents) => 
    pp_info_box(pp_newline, `Warning, pp_nestable_block_element(~resolveLink), formatter, [{value: `Paragraph([{value: `Word("Raises " ++ name ++ " : "), location: tag.location}]), location: tag.location}, ...contents])

  | `Before(version, contents) =>
    pp_info_box(pp_newline, `Note, pp_nestable_block_element(~resolveLink), formatter, [{value: `Paragraph([{value: `Word("Before " ++ version ++ " : "), location: tag.location}]), location: tag.location}, ...contents])

  | `Return(contents) => 
    pp_info_box(pp_newline, `Note, pp_nestable_block_element(~resolveLink), formatter, [{value: `Paragraph([{value: `Word("Returns: "), location: tag.location}]), location: tag.location},  ...contents])

  | `See(_, link, contents) => 
    pp_info_box(pp_newline, `Important, pp_nestable_block_element(~resolveLink), formatter, [{value: `Paragraph([{value: `Link(link, [{location: tag.location, value: `Word("See: ")}]), location: tag.location}]), location: tag.location},  ...contents])

  | `Since(versionString) => 
    pp_info_box(pp_newline, `Note, (_) => pp_inline_ele(~resolveLink), formatter, [{value: `Word("Since: " ++ versionString), location: tag.location}])

  | `Version(versionString) => 
    pp_info_box(pp_newline, `Note, (_) => pp_inline_ele(~resolveLink), formatter, [{value: `Word("Version: " ++ versionString), location: tag.location}])

  | _ => ()
}

and pp_block_element = (~resolveLink, pp_newline, formatter, element: Loc.with_location(Ast.block_element)) => {
  switch (element.value) {
    | `Heading(level, _label, content) => pp_heading(~resolveLink, formatter, level, content)
    | `Tag(tag) => pp_tag(~resolveLink, pp_newline, formatter, {...element, value: tag})
    | #Ast.nestable_block_element as desc => pp_nestable_block_element(~resolveLink, pp_newline, formatter, {...element, value: desc})
  }
}

and pp_block_elements = (~resolveLink, pp_newline, formatter, elements: list(Loc.with_location(Ast.block_element))) =>
  Format.pp_print_list(~pp_sep=pp_block_delimit(pp_newline), pp_block_element(~resolveLink, pp_newline), formatter, elements)

and pp_block_elements_in_list = (~resolveLink, pp_newline, formatter, elements: list(Loc.with_location(Ast.block_element))) =>
  Format.pp_print_list(~pp_sep=pp_block_list_delimit(pp_newline), pp_block_element(~resolveLink, pp_newline), formatter, elements);

let pp_warning = (~location, pp_newline, formatter, warning: Odoc_parser.Warning.t) => {
  let uri = "file://" ++ location.Lexing.pos_fname ++ "#L" ++ string_of_int(warning.location.start.line) ++ "%2C" ++ string_of_int(warning.location.start.column);

  Format.fprintf(formatter, "[Warning at %d:%d](<%s>): %s", warning.location.start.line, warning.location.start.column, uri, warning.message);
}

let pp_warning_box = (~location, pp_newline, formatter, warning) => pp_info_box(pp_newline, `Warning, pp_warning(~location), formatter, [warning]);

let pp_warnings = (~location, pp_newline, formatter, warnings) => Format.pp_print_list(~pp_sep=pp_block_delimit(pp_newline), pp_warning_box(~location, pp_newline), formatter, warnings);

let convert = (~location=?, ~resolveLink, text) => {
  let prev_margin = Format.pp_get_margin(Format.str_formatter, ());
  Format.pp_set_margin(Format.str_formatter, Int.max_int);

  let location = location->Belt.Option.mapWithDefault(Lexing.dummy_pos, loc => loc.Compiler_libs_406.Location.loc_start);
  try {
    let res = Odoc_parser.parse_comment(
      ~location,
      ~text
    );
    let items = res |> Odoc_parser.ast;
    let warnings = res|> Odoc_parser.warnings;

    Format.fprintf(Format.str_formatter, "%a%a%a------%a%a", pp_block_elements(~resolveLink, Format.pp_force_newline), items, Format.pp_force_newline, (), Format.pp_force_newline, (), Format.pp_force_newline, (), pp_warnings(~location, Format.pp_force_newline), warnings);
  } {
    | exn => Format.fprintf(Format.str_formatter, "Error (invalid syntax?) while parsing ocamldoc: %s", Printexc.to_string(exn));
  }

  let res = Format.flush_str_formatter();

  Format.pp_set_margin(Format.str_formatter, prev_margin);
  res;
};

