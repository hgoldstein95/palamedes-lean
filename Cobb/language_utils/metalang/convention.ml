open Sugar
open Ocaml5_parser
open Parsetree
open Mutils

let escape_to_underscore str =
  String.of_seq
  @@ Seq.filter_map (fun x ->
         match x with
         | '.' -> Some '_'
         | ',' -> Some '_'
         | ' ' -> None
         | '\'' -> Some '_'
         | '(' -> None
         | ')' -> None
         | c -> Some (Char.lowercase_ascii c))
  @@ String.to_seq str

let mk_func_name (auxname : string) (tyname : string) =
  spf "%s_%s" auxname tyname

let mk_typed_func_name (auxname : string) (tyname : string) =
  spf "typed_%s" (mk_func_name auxname tyname)

let mk_var_name (name : string) (tyname : string) =
  spf "%s_%s" (escape_to_underscore tyname) (escape_to_underscore name)

let mk_tmp_name (idx : int) (tyname : string) =
  spf "%s%i" (escape_to_underscore tyname) idx

let split_ct_attr (ct : core_type) =
  let ct' = { ct with ptyp_attributes = [] } in
  if exists_attributes ct.ptyp_attributes "bound" then (Some "bound", ct')
  else if exists_attributes ct.ptyp_attributes "free" then (Some "free", ct')
  else (None, ct')

open Sugar

let get_tyname_from_predefine f predefine =
  List.fold_left
    (fun res (x, name) ->
      match res with None -> if f x then Some name else None | Some _ -> res)
    None predefine

type predef = PreDefTyped of string | PreDefPlain of string

let mk_predefine type_name =
  match type_name with
  | PreDefPlain type_name ->
      let fname selfname = mk_func_name selfname type_name in
      let plain_ty = mk_ty_constr type_name [] in
      [ (plain_ty, fname) ]
  | PreDefTyped type_name ->
      let fname selfname = mk_func_name selfname type_name in
      let typed_fname selfname = mk_typed_func_name selfname type_name in
      let ty = mk_ty_constr type_name [ var_to_ct "t" ] in
      let typed_ty = mk_ty_constr "typed" [ var_to_ct "t"; ty ] in
      [ (ty, fname); (typed_ty, typed_fname) ]

let mk_predefines l = List.concat @@ List.map mk_predefine l

let pcd_args_to_args pcd_args =
  match pcd_args with
  | Pcstr_tuple cts ->
      List.mapi
        (fun idx ct -> (mk_tmp_name idx (layout_ct (clear_ct_attr ct)), ct))
        cts
  | Pcstr_record lds ->
      List.map (fun ld -> (ld.pld_name.Location.txt, ld.pld_type)) lds

let layout_tyd tyd =
  Pprintast.string_of_structure
  @@ [ desc_to_structure_item @@ Pstr_type (Asttypes.Recursive, [ tyd ]) ]

open Zzdatatype.Datatype

type tyd_context_item = {
  mk_t_typed : core_type -> core_type;
  ty : core_type;
  typed_ty : core_type;
  has_typed : bool;
  cs : constructor_declaration list;
}

let get_ty_name_from_ctx (f : core_type -> bool) ctx =
  StrMap.fold
    (fun tyname { ty; _ } res ->
      match res with
      | Some _ -> res
      | None -> if f ty then Some tyname else None)
    ctx None

type tyd_context = tyd_context_item StrMap.t

let tyd_to_cs tyd =
  match tyd.ptype_kind with
  | Ptype_variant cs -> cs
  | _ ->
      Printf.printf "%s\n" (layout_tyd tyd);
      _failatwith __FILE__ __LINE__ "unimp "

let tyd_to_ctx (tyds : type_declaration list) =
  let l =
    List.map
      (fun tyd ->
        let type_name = tyd.ptype_name.Location.txt in
        let ty = get_ty_from_type_dedeclaration tyd in
        let has_typed = match tyd.ptype_params with [] -> false | _ -> true in
        let mk_t_typed ty =
          match tyd.ptype_params with
          | [] -> ty
          | _ -> mk_ty_constr "typed" (List.map fst tyd.ptype_params @ [ ty ])
        in
        let typed_ty = mk_t_typed ty in
        let cs = tyd_to_cs tyd in
        (type_name, { has_typed; mk_t_typed; ty; typed_ty; cs }))
      tyds
  in
  StrMap.from_kv_list l

type constrh = {
  cargs : (string * core_type) list;
  cmkpat : pattern option list -> pattern;
  cmke : expression option list -> expression;
}

let mk_first_match target_e (f : constrh -> pattern * expression)
    (cs : constructor_declaration list) : expression =
  let cs =
    List.map
      (fun { pcd_name; pcd_args; _ } ->
        let name = pcd_name.Location.txt in
        match pcd_args with
        | Pcstr_tuple cts ->
            let cargs =
              List.mapi
                (fun idx ct ->
                  (mk_tmp_name idx (layout_ct (clear_ct_attr ct)), ct))
                cts
            in
            let cmkpat pats =
              let pats =
                List.map
                  (fun pat ->
                    match pat with
                    | None -> string_to_pattern "_"
                    | Some pat -> pat)
                  pats
              in
              string_dataconstr_to_pattern (name, pats)
            in
            let cmke es =
              let es =
                List.map
                  (fun pat ->
                    match pat with None -> mkvar "_" | Some pat -> pat)
                  es
              in
              mk_construct (name, es)
            in
            let lhs, e = f { cargs; cmkpat; cmke } in
            (lhs, e)
        | Pcstr_record lds ->
            let cargs =
              List.map (fun ld -> (ld.pld_name.Location.txt, ld.pld_type)) lds
            in
            let cmkpat pats =
              let pats =
                List.map (fun ((lab, _), pat) ->
                    let lab = Location.mknoloc (Longident.Lident lab) in
                    (lab, pat))
                @@ List.combine cargs pats
              in
              string_dataconstr_to_pattern
                (name, [ string_record_to_pattern pats ])
            in
            let cmke es =
              let es =
                List.map
                  (fun x ->
                    match x with
                    | Some x -> x
                    | None -> _failatwith __FILE__ __LINE__ "never")
                  es
              in
              let es =
                List.map (fun ((lab, _), pat) ->
                    let lab = Location.mknoloc (Longident.Lident lab) in
                    (lab, pat))
                @@ List.combine cargs es
              in
              mk_op_apply (name, [ desc_to_ocamlexpr @@ Pexp_record (es, None) ])
            in
            let lhs, e = f { cargs; cmkpat; cmke } in
            (lhs, e))
      cs
  in
  mk_match target_e cs

let mk_ite_swtich nonse (f, res) =
  ((fun ct -> if f ct then Some nonse else None), fun _ -> res)

let match_ct_switch (ct : core_type) (default, l) =
  List.fold_left
    (fun res (f, resf) -> match f ct with Some r -> resf r | None -> res)
    default l
