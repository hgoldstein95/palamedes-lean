open Core
open Caux
open Language
open Zzdatatype.Datatype
open Preprocessing.Normal_item_typing
open To_item
open Raw_term_to_anf

let parse = Ocaml5_parser.Frontend.parse

let preprocess source_file () =
  let prim_path = Env.get_prim_path () in
  let s1 = parse ~sourcefile:prim_path.type_decls in
  let s2 = parse ~sourcefile:prim_path.normal_typing in
  let init_normal_ctx =
    struct_mk_ctx Typectx.emp (ocaml_structure_to_items (s1 @ s2))
  in
  let code =
    ocaml_structure_to_items
    @@ Ocaml5_parser.Frontend.parse ~sourcefile:source_file
  in
  (* let _ = Pp.printf "%s\n" (FrontendRaw.layout_structure code) in *)
  let _, code = struct_check init_normal_ctx code in
  (* let _ = Pp.printf "%s\n" (FrontendTyped.layout_structure code) in *)
  let code = normalize_structure code in
  (* let _ = Pp.printf "%s\n" (FrontendTyped.layout_structure code) in *)
  code

let print_source_code meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let _ = preprocess source_file () in
  ()

let subtype_check_ meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = preprocess source_file () in
  let prim_path = Env.get_prim_path () in
  let predefine = preprocess prim_path.coverage_typing () in
  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in
  let axioms = preprocess prim_path.axioms () in
  let axioms =
    List.map (fun x -> x.ty) @@ Typing.Itemcheck.gather_axioms axioms
  in
  let _, rty1 = get_rty_by_name code "rty1" in
  let _, rty2 = get_rty_by_name code "rty2" in
  let ctx = FrontendTyped.{ builtin_ctx; local_ctx = emp; axioms } in
  let res = Subtyping.Subrty.sub_rty_bool ctx (rty1, rty2) in
  let () = FrontendTyped.pprint_typectx_subtyping emp (rty1, rty2) in
  let () =
    Printf.printf "%s <: %s\n"
      (FrontendTyped.layout_rty rty1)
      (FrontendTyped.layout_rty rty2)
  in
  let () = Printf.printf "Result: %b\n" res in
  ()

let rec_arg_list = [ "rec_arg"; "rec_arg2" ]

let handle_template templates =
  let templates = Typing.Itemcheck.gather_axioms templates in
  let rec_arg_temp =
    List.map
      (fun y ->
        match List.find_opt (fun x -> String.equal x.x y) templates with
        | None ->
            failwith (Sugar.spf "cannot find builtin rec arg constraints: %s" y)
        | Some x -> (x.x, x.ty))
      rec_arg_list
  in
  let () = Typing.Termcheck.init_rec_arg rec_arg_temp in
  let temp_names = Env.get_uninterops () in
  let templates =
    List.map
      (fun name ->
        match List.find_opt (fun x -> String.equal name x.x) templates with
        | None -> Sugar._failatwith __FILE__ __LINE__ "die"
        | Some x -> x.ty)
      temp_names
  in
  templates

let handle_lemma axioms =
  let axioms =
    List.map (fun x -> x.ty) @@ Typing.Itemcheck.gather_axioms axioms
  in
  axioms

let type_check_ meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = preprocess source_file () in
  let prim_path = Env.get_prim_path () in
  let predefine = preprocess prim_path.coverage_typing () in
  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in
  let axioms = preprocess prim_path.axioms () in
  let axioms = handle_lemma axioms in
  let templates = preprocess prim_path.templates () in
  let templates = handle_template templates in
  let () = Inference.Feature.init_template templates in
  let _ = Typing.Itemcheck.struc_check (axioms, builtin_ctx) code in
  ()

let type_infer_inner meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = preprocess source_file () in
  let prim_path = Env.get_prim_path () in
  let predefine = preprocess prim_path.coverage_typing () in
  let builtin_ctx = Typing.Itemcheck.gather_uctx predefine in
  let axioms = preprocess prim_path.axioms () in
  let axioms = handle_lemma axioms in
  let templates = preprocess prim_path.templates () in
  let templates = handle_template templates in
  let () = Inference.Feature.init_template templates in
  let _ = Typing.Itemcheck.struc_infer (axioms, builtin_ctx) code in
  let result = Typing.Termsyn.get_inferred_result () in
  result

let type_infer_ meta_config_file source_file () =
  let result = type_infer_inner meta_config_file source_file () in
  let () =
    let oc = Out_channel.create @@ Env.get_abdfile source_file in
    Printf.fprintf oc "%s\n" (FrontendTyped.layout_rty result);
    Out_channel.close oc
  in
  ()

let coq_axioms meta_config_file () =
  let () = Env.load_meta meta_config_file in
  let prim_path = Env.get_prim_path () in
  let axioms : t item list = preprocess prim_path.axioms () in

  print_endline "Axioms:";
  List.iter
    (fun x -> Printf.printf "%s\n" (FrontendTyped.layout_item_to_coq x))
    axioms;
  ()

let print_erase_code meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code =
    ocaml_structure_to_items
    @@ Ocaml5_parser.Frontend.parse ~sourcefile:source_file
  in
  let code = List.map item_erase code in
  let _ = Printf.printf "%s\n" (FrontendRaw.layout_structure code) in
  ()

let input_config message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open meta_config_file =
        anon ("meta_config_file" %: regular_file)
      in
      f meta_config_file)

let input_config_source message f =
  Command.basic ~summary:message
    Command.Let_syntax.(
      let%map_open meta_config_file = anon ("meta_config_file" %: regular_file)
      and source_file = anon ("source_code_file" %: regular_file) in
      f meta_config_file source_file)

let print_source_code =
  Command.group ~summary:"print source code"
    [
      ("raw", input_config_source "print raw source code" print_source_code);
      ("erase", input_config_source "print erase source code" print_erase_code);
    ]

let test =
  Command.group ~summary:"Poirot"
    [
      ("print-source-code", print_source_code);
      ("type-check", input_config_source "type check" type_check_);
      ("type-infer", input_config_source "type infer" type_infer_);
      ("subtype-check", input_config_source "subtype check" subtype_check_);
      ("coq-axioms", input_config "coq axioms" coq_axioms);
    ]
