open Ocaml5_parser
open Mutils
open Parsetree
open Convention
(* open Sugar *)

let selfname = "fv"

type varset =
  | Pos of (pattern * expression)
  | Neg of (pattern * expression)
  | Unused

let mk predefine (type_name, { has_typed; ty; typed_ty; cs; mk_t_typed }) =
  let var_eq =
    if has_typed then mk_op_apply ("typed_eq", [ mkvar "String.equal" ])
    else mkvar "String.equal"
  in
  let func_name = mk_func_name selfname type_name in
  let typed_func_name = mk_typed_func_name selfname type_name in
  let e_name = mk_var_name "e" type_name in
  let f_one (arg, ct) =
    let default = Unused in
    let arg_term = mkvar arg in
    let attr, ct = split_ct_attr ct in
    let arg_pat = string_to_pattern arg in
    let mk_ite_swtich = mk_ite_swtich (fun _ -> "") in
    let typed_cases =
      if has_typed then
        [
          mk_ite_swtich
            ( ct_eq (mk_t_typed ty_var),
              match attr with
              | Some "free" -> Pos (arg_pat, mk_list_literal [ arg_term ])
              | Some "bound" -> Neg (arg_pat, mk_list_literal [ arg_term ])
              | _ -> default );
          mk_ite_swtich
            ( ct_eq (mk_ty_list (mk_t_typed ty_var)),
              match attr with
              | Some "free" -> Pos (arg_pat, arg_term)
              | Some "bound" -> Neg (arg_pat, arg_term)
              | _ -> default );
        ]
      else []
    in
    match_ct_switch ct
      ( default,
        typed_cases
        @ [
            mk_ite_swtich
              ( ct_eq ty_var,
                match attr with
                | Some "free" -> Pos (arg_pat, mk_list_literal [ arg_term ])
                | Some "bound" -> Neg (arg_pat, mk_list_literal [ arg_term ])
                | _ -> default );
            ( (fun ct -> get_tyname_from_predefine (ct_eq ct) predefine),
              fun fname ->
                Pos (arg_pat, mk_op_apply (fname selfname, [ mkvar arg ])) );
            ( (fun ct ->
                get_tyname_from_predefine
                  (fun ty -> ct_eq ct (mk_ty_list ty))
                  predefine),
              fun fname ->
                Pos
                  ( arg_pat,
                    mk_list_concat_apply
                    @@ mk_list_map_apply (mkvar @@ fname selfname) arg_term ) );
          ] )
  in
  let f { cargs = args; cmkpat; _ } =
    let res = List.map f_one args in
    let args =
      List.fold_left
        (fun args res ->
          match res with
          | Unused -> args @ [ None ]
          | Pos (name, _) -> args @ [ Some name ]
          | Neg (name, _) -> args @ [ Some name ])
        [] res
    in
    let body =
      List.fold_right
        (fun res body ->
          match res with
          | Unused -> body
          | Pos (_, e) -> mk_list_union_apply body e
          | Neg (_, e) -> mk_list_subtract_apply var_eq body e)
        res mk_empty_list
    in
    let lhs = cmkpat args in
    (lhs, body)
  in
  let body = mk_first_match (mkvar e_name) f cs in
  let fv_def = (func_name, [ (e_name, Some ty) ], body) in
  if has_typed then
    let typed_fv_def =
      ( typed_func_name,
        [ (e_name, Some typed_ty) ],
        mk_op_apply (func_name, [ mkvar (e_name ^ ".x") ]) )
    in
    [ fv_def; typed_fv_def ]
  else [ fv_def ]
