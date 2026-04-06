open Ocaml5_parser
open Convention
open Mutils
open Sugar

let selfname = "subst"

let mk predefine (type_name, { has_typed; ty; typed_ty; cs; mk_t_typed }) =
  let x_ty = ty_var in
  (* let f_ty = mk_arrty (mk_t_typed x_ty) ty in *)
  let func_name = mk_func_name selfname type_name in
  let typed_func_name = mk_typed_func_name selfname type_name in
  let x_name = mk_var_name "x" "string" in
  let f_name = "f" in
  let e_name = mk_var_name "e" type_name in
  let x_term, f_term, e_term = map3 mkvar (x_name, f_name, e_name) in
  let f { cargs = args; cmkpat; cmke } =
    let rec aux (is_closed, args', args) =
      match args with
      | [] -> cmke (List.map (fun x -> Some x) args')
      | (arg, ct) :: args ->
          let arg_term = mkvar arg in
          let attr, ct = split_ct_attr ct in
          let ret b x = aux (b, args' @ [ x ], args) in
          let default = ret false arg_term in
          if is_closed then ret true arg_term
          else
            let mk_ite_swtich = mk_ite_swtich (fun _ -> "") in
            let typed_cases =
              if has_typed then
                [
                  mk_ite_swtich
                    ( ct_eq (mk_t_typed ty_var),
                      let cond =
                        mk_op_apply
                          ("String.equal", [ mkvar (arg ^ ".x"); x_term ])
                      in
                      match attr with
                      | Some "free" ->
                          mk_ite
                            ( cond,
                              mk_op_apply (f_name, [ arg_term ]),
                              ret false arg_term )
                      | Some "bound" -> mk_ite (cond, ret true arg_term, default)
                      | _ -> default );
                  mk_ite_swtich
                    ( ct_eq (mk_ty_list (mk_t_typed ty_var)),
                      let cond =
                        mk_op_apply
                          ( "List.exists",
                            [
                              mklam (string_to_pattern "x")
                                (mk_op_apply
                                   ("String.equal", [ x_term; mkvar "x.x" ]));
                              arg_term;
                            ] )
                      in
                      match attr with
                      | Some "bound" -> mk_ite (cond, ret true arg_term, default)
                      | _ ->
                          (* Printf.printf "%s\n" (layout_ct ct); *)
                          default );
                ]
              else []
            in
            match_ct_switch ct
              ( default,
                typed_cases
                @ [
                    mk_ite_swtich
                      ( ct_eq ty_var,
                        let cond =
                          mk_op_apply ("String.equal", [ mkvar arg; x_term ])
                        in
                        match attr with
                        | Some "free" ->
                            mk_ite
                              ( cond,
                                mk_op_apply (f_name, [ arg_term ]),
                                ret false arg_term )
                        | Some "bound" ->
                            mk_ite (cond, ret true arg_term, default)
                        | _ -> default );
                    ( (fun ct ->
                        get_tyname_from_predefine
                          (fun prect ->
                            (*   let () = *)
                            (*     Printf.printf "ct: %s ?= prect : %s\n" *)
                            (*       (layout_ct ct) (layout_ct prect) *)
                            (*   in *)
                            ct_eq ct prect)
                          predefine),
                      fun fname ->
                        ret false
                          (mk_op_apply
                             (fname selfname, [ x_term; f_term; arg_term ])) );
                    ( (fun ct ->
                        get_tyname_from_predefine
                          (fun ty -> ct_eq ct (mk_ty_list ty))
                          predefine),
                      fun fname ->
                        ret false
                          (mk_list_map_apply
                             (mk_op_apply (fname selfname, [ x_term; f_term ]))
                             arg_term) );
                  ] )
    in
    let body = aux (false, [], args) in
    let lhs =
      cmkpat (List.map (fun (x, _) -> Some (string_to_pattern x)) args)
    in
    (lhs, body)
  in
  let body = mk_first_match e_term f cs in
  let subst_def =
    (func_name, [ (x_name, Some x_ty); (f_name, None); (e_name, Some ty) ], body)
  in
  let typed_body =
    mk_typed_map e_term @@ mk_op_apply (func_name, [ x_term; f_term ])
  in
  if has_typed then
    let typed_subst_def =
      ( typed_func_name,
        [ (x_name, Some x_ty); (f_name, None); (e_name, Some typed_ty) ],
        typed_body )
    in
    [ subst_def; typed_subst_def ]
  else [ subst_def ]
