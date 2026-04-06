open Convention
open Ocaml5_parser
open Mutils
(* open Sugar *)

let selfname = "fv"

let mk _ (type_name, { has_typed; _ }) =
  if not has_typed then []
  else
    let func_name = mk_func_name selfname type_name in
    let typed_func_name = mk_typed_func_name selfname type_name in
    let e_name = "e" in
    let fv_def =
      ( func_name ^ "_id",
        [ (e_name, None) ],
        mk_op_apply ("fv_typed_id_to_id", [ mkvar func_name; mkvar e_name ]) )
    in
    let res =
      if has_typed then
        let typed_fv_def =
          ( typed_func_name ^ "_id",
            [ (e_name, None) ],
            mk_op_apply
              ("fv_typed_id_to_id", [ mkvar typed_func_name; mkvar e_name ]) )
        in
        [ fv_def; typed_fv_def ]
      else [ fv_def ]
    in
    List.map mk_funcdef_args res
