(* let mk_eq_match target_e *)
(*     (f : string * (string * core_type) list -> pattern * expression) *)
(*     (tyd : type_declaration) : expression = *)
(*   let cs = *)
(*     List.map *)
(*       (fun { pcd_name; pcd_args; _ } -> *)
(*         let name = pcd_name.Location.txt in *)
(*         let args = pcd_args_to_args pcd_args in *)
(*         (name, args)) *)
(*       (tyd_to_cs tyd) *)
(*   in *)
(*   mk_match target_e @@ List.map f cs *)

(* let mk_eq_match (target_e1, target_e2) *)
(*     (f : *)
(*       string -> *)
(*       ((string * string) * core_type) list -> *)
(*       (string * string) list * expression) (tyd : type_declaration) : expression *)
(*     = *)
(*   let cs = *)
(*     match tyd.ptype_kind with *)
(*     | Ptype_variant cs -> cs *)
(*     | _ -> _failatwith __FILE__ __LINE__ "unimp" *)
(*   in *)
(*   let cs = *)
(*     List.map *)
(*       (fun { pcd_name; pcd_args; _ } -> *)
(*         let name = pcd_name.Location.txt in *)
(*         let args = *)
(*           match pcd_args with *)
(*           | Pcstr_tuple cts -> *)
(*               List.mapi *)
(*                 (fun idx ct -> *)
(*                   let name = mk_tmp_name idx (layout_ct (clear_ct_attr ct)) in *)
(*                   ((name, name ^ "'"), ct)) *)
(*                 cts *)
(*           | _ -> _failatwith __FILE__ __LINE__ "unimp" *)
(*         in *)
(*         (name, args)) *)
(*       cs *)
(*   in *)
(*   mk_match (mktuple [ target_e1; target_e2 ]) *)
(*   @@ List.map (fun (dtname, args) -> (dtname, f dtname args)) cs *)

let mk_eq (tyd : type_declaration) : structure =
  let selfname = "eq" in
  let ty = get_ty_from_type_dedeclaration tyd in
  let mk_t_typed ty =
    mk_ty_constr "typed" (List.map fst tyd.ptype_params @ [ ty ])
  in
  let type_name = tyd.ptype_name.Location.txt in
  let func_name = mk_func_name selfname type_name in
  let e1_name = mk_var_name "e1" type_name in
  let e2_name = mk_var_name "e2" type_name in
  let f_one (arg, ct) =
    if ct_eq ty ct then (true, mk_op_apply (func_name, [ mkvar arg ]))
    else
      match ct.ptyp_desc with
      | Ptyp_constr (dt, ct') -> (
          match (Longident.flatten dt.Location.txt, ct') with
          | [ "typed" ], [ ct_x; _ ] ->
              if exists_attributes ct_x.ptyp_attributes "free" then
                (true, mk_op_apply ("::", [ mkvar arg; mk_empty_list ]))
              else (false, mk_empty_list)
          | [ "list" ], [ ct' ] when ct_eq (mk_t_typed ty) ct' ->
              ( true,
                mk_op_apply
                  ( "List.concat",
                    [ mk_op_apply ("List.map", [ mkvar func_name; mkvar arg ]) ]
                  ) )
          | [ "list" ], [ ct' ] when ct_eq ty ct' ->
              ( true,
                mk_op_apply
                  ( "List.concat",
                    [ mk_op_apply ("List.map", [ mkvar func_name; mkvar arg ]) ]
                  ) )
          | _ -> (false, mk_empty_list))
      | _ -> (false, mk_empty_list)
  in
  let f _ args =
    let if_used, body = List.split @@ List.map f_one args in
    let args_name =
      List.map
        (fun (if_used, (name, _)) -> if if_used then name else "_")
        (List.combine if_used args)
    in
    let body =
      List.fold_left
        (fun res e -> mk_op_apply ("@", [ res; e ]))
        mk_empty_list body
    in
    (args_name, body)
  in
  let body = mk_first_match (mktuple [ mkvar e1_name; mkvar e2_name ]) f tyd in
  let fv_def =
    mk_rec_funcdef_args func_name [ (e1_name, ty); (e2_name, ty) ] body
  in
  let typed_fv_def =
    mk_funcdef_args
      (mk_typed_func_name selfname type_name)
      [ (e1_name, ty); (e2_name, ty) ]
      (mk_op_apply
         (func_name, [ mkvar (e1_name ^ ".x"); mkvar (e2_name ^ ".x") ]))
  in
  [ fv_def; typed_fv_def ]
