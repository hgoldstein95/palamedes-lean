open Ocaml5_parser
open Convention
open Mutils
open Sugar

let selfname = "map"
let poly_t = "t"
let poly_t' = "s"

let mk predefine (type_name, { has_typed; ty; typed_ty; cs; mk_t_typed }) =
  if not has_typed then []
  else
    let f_ty = mk_arrty (var_to_ct poly_t) (var_to_ct poly_t') in
    let main_name = mk_func_name selfname type_name in
    let typed_main_name = mk_typed_func_name selfname type_name in
    let f_name = "f" in
    let e_name = mk_var_name "e" type_name in
    let f_term, e_term = map2 mkvar (f_name, e_name) in
    let f { cargs = args; cmkpat; cmke } =
      let rec aux (args', args) =
        match args with
        | [] -> cmke (List.map (fun x -> Some x) args')
        | (arg, ct) :: args ->
            let arg_term = mkvar arg in
            let ret x = aux (args' @ [ x ], args) in
            let default = ret arg_term in
            let apply_f term = mk_op_apply ("#=>", [ term; f_term ]) in
            let mk_ite_swtich = mk_ite_swtich (fun _ -> "") in
            match_ct_switch ct
              ( default,
                [
                  mk_ite_swtich
                    (ct_eq (mk_t_typed ty_var), ret @@ apply_f arg_term);
                  mk_ite_swtich
                    ( ct_eq (mk_ty_list (mk_t_typed ty_var)),
                      ret
                      @@ mk_list_map_apply
                           (mklam (string_to_pattern "x") (apply_f (mkvar "x")))
                           arg_term );
                  ( (fun ct -> get_tyname_from_predefine (ct_eq ct) predefine),
                    fun fname ->
                      ret (mk_op_apply (fname selfname, [ f_term; arg_term ]))
                  );
                  ( (fun ct ->
                      get_tyname_from_predefine
                        (fun ty -> ct_eq ct (mk_ty_list ty))
                        predefine),
                    fun fname ->
                      ret
                        (mk_list_map_apply
                           (mk_op_apply (fname selfname, [ f_term ]))
                           arg_term) );
                ] )
      in
      let body = aux ([], args) in
      let lhs =
        cmkpat (List.map (fun (x, _) -> Some (string_to_pattern x)) args)
      in
      (lhs, body)
    in
    let body = mk_first_match e_term f cs in
    let main_def =
      (main_name, [ (f_name, Some f_ty); (e_name, Some ty) ], body)
    in
    let typed_body =
      mk_typed_map e_term @@ mk_op_apply (main_name, [ f_term ])
    in
    if has_typed then
      let typed_main_def =
        ( typed_main_name,
          [ (f_name, Some f_ty); (e_name, Some typed_ty) ],
          typed_body )
      in
      [ main_def; typed_main_def ]
    else [ main_def ]
