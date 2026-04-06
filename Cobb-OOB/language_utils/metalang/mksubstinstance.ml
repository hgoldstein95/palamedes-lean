open Convention
open Ocaml5_parser
open Mutils

let selfname = "subst"

let mk _ (type_name, { has_typed; _ }) =
  let func_name = mk_func_name selfname type_name in
  let typed_func_name = mk_typed_func_name selfname type_name in
  let x_name = "x" in
  let instance_name = "instance" in
  let e_name = "e" in
  let fv_def =
    ( func_name ^ "_instance",
      [ (x_name, None); (instance_name, None); (e_name, None) ],
      mk_op_apply
        ( "subst_f_to_instance",
          [ mkvar func_name; mkvar x_name; mkvar instance_name; mkvar e_name ]
        ) )
  in
  let res =
    if has_typed then
      let typed_fv_def =
        ( typed_func_name ^ "_instance",
          [ (x_name, None); (instance_name, None); (e_name, None) ],
          mk_op_apply
            ( "subst_f_to_instance",
              [
                mkvar typed_func_name;
                mkvar x_name;
                mkvar instance_name;
                mkvar e_name;
              ] ) )
      in
      [ fv_def; typed_fv_def ]
    else [ fv_def ]
  in
  List.map mk_funcdef_args res
