open Language
open FrontendTyped

(* open Zzdatatype.Datatype *)
open Sugar

(* open Subtyping *)
open Termcheck

type t = Nt.t

let layout_ty = Nt.layout
let inferred_result = ref None

let get_inferred_result () =
  match !inferred_result with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some res -> res

let rec partial_value_type_infer (uctx : uctx) (a : (t, t value) typed)
    (rty : t rty) : (t rty, t rty value) typed option =
  let res =
    match (a.x, rty) with
    | VLam { lamarg; body }, RtyBaseArr { argcty; arg; retty } ->
        let body =
          body #-> (subst_term_instance lamarg.x (VVar arg #: lamarg.ty))
        in
        (* let retty = subst_rty_instance arg (AVar lamarg) retty in *)
        let argrty = RtyBase { ou = true; cty = argcty } in
        let* body =
          partial_term_type_infer (add_to_right uctx arg #: argrty) body retty
        in
        let lamarg = arg #: argrty in
        let rty = RtyBaseArr { argcty; arg; retty = body.ty } in
        Some (VLam { lamarg; body }) #: rty
    | VLam { lamarg; body }, RtyArrArr { argrty; retty } ->
        let* body =
          partial_term_type_infer
            (add_to_right uctx lamarg.x #: argrty)
            body retty
        in
        let lamarg = lamarg.x #: argrty in
        let rty = RtyArrArr { argrty; retty = body.ty } in
        Some (VLam { lamarg; body }) #: rty
    | VLam _, _ -> _failatwith __FILE__ __LINE__ ""
    | VFix { fixname; fixarg; body }, RtyBaseArr { argcty; arg; retty } ->
        let _, ret_nty = Nt.destruct_arr_tp fixname.ty in
        (* For STLC, we use a different recursion template *)
        if String.equal "stlc_term" (layout_ty ret_nty) then
          match (body.x, retty) with
          | ( CVal { x = VLam { lamarg; body }; _ },
              RtyBaseArr { argcty = argcty1; arg = arg1; retty } ) ->
              let rty' =
                let arg' = { x = Rename.unique arg; ty = fixarg.ty } in
                let arg = arg #: fixarg.ty in
                let arg1' = { x = Rename.unique arg1; ty = lamarg.ty } in
                let arg1 = arg1 #: lamarg.ty in
                let rec_constraint_cty = apply_rec_arg2 arg arg' arg1 in
                RtyBaseArr
                  {
                    argcty;
                    arg = arg'.x;
                    retty =
                      RtyBaseArr
                        {
                          argcty =
                            intersect_ctys [ argcty1; rec_constraint_cty ];
                          arg = arg1'.x;
                          retty =
                            subst_rty_instance arg1.x (AVar arg1')
                            @@ subst_rty_instance arg.x (AVar arg') retty;
                        };
                  }
              in
              let binding = arg #: (RtyBase { ou = true; cty = argcty }) in
              let binding1 = arg1 #: (RtyBase { ou = true; cty = argcty1 }) in
              let body =
                body
                #-> (subst_term_instance fixarg.x (VVar arg #: fixarg.ty))
                #-> (subst_term_instance lamarg.x (VVar arg1 #: fixarg.ty))
              in
              let* body' =
                partial_term_type_infer
                  (add_to_rights uctx [ binding; binding1; fixname.x #: rty' ])
                  body retty
              in
              let lam =
                (VLam { lamarg = binding1; body = body' })
                #: (RtyBaseArr { argcty = argcty1; arg = arg1; retty })
              in
              let clam = (CVal lam) #: lam.ty in
              Some
                (VFix
                   { fixname = fixname.x #: rty; fixarg = binding; body = clam })
                #: rty
          | _ -> _failatwith __FILE__ __LINE__ "die"
        else
          let rec_constraint_cty = apply_rec_arg1 arg #: fixarg.ty in
          let rty' =
            let a = { x = Rename.unique arg; ty = fixarg.ty } in
            RtyBaseArr
              {
                argcty = intersect_ctys [ argcty; rec_constraint_cty ];
                arg = a.x;
                retty = subst_rty_instance arg (AVar a) retty;
              }
          in
          let binding = arg #: (RtyBase { ou = true; cty = argcty }) in
          let body =
            body #-> (subst_term_instance fixarg.x (VVar arg #: fixarg.ty))
          in
          let* body' =
            partial_term_type_infer
              (add_to_rights uctx [ binding; fixname.x #: rty' ])
              body retty
          in
          let rty = RtyBaseArr { argcty; arg; retty = body'.ty } in
          Some
            (VFix { fixname = fixname.x #: rty; fixarg = binding; body = body' })
            #: rty
    | _ -> Some (value_type_infer uctx a)
  in
  let () =
    match res with
    | Some res -> pprint_simple_typectx_infer uctx (layout_typed_value a, res.ty)
    | None -> ()
  in
  res

and partial_term_type_infer (uctx : uctx) (a : (t, t term) typed) (rty : t rty)
    : (t rty, t rty term) typed option =
  match a.x with
  | CVal v ->
      let* v = partial_value_type_infer uctx v rty in
      Some (CVal v) #: v.ty
  | _ ->
      (* NOTE: the first type not a value (function body) *)
      let* a = term_type_infer uctx a in
      let inferred_rty = Infer_prop.abductive_infer_rty uctx a.ty rty in
      let () = Printf.printf "inferred_rty: %s\n" (layout_rty inferred_rty) in
      let () = inferred_result := Some inferred_rty in
      Some a
(* | _ -> term_type_infer uctx a *)
