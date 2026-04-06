open Ocaml5_parser
open Mutils
open Convention
open Sugar

let selfname = "equal"

let mk _ (type_name, { has_typed; _ }) =
  if has_typed then []
  else
    let func_name = mk_func_name selfname type_name in
    (* let typed_func_name = mk_typed_func_name selfname type_name in *)
    let sexp_name = spf "sexp_of_%s" type_name in
    let e1_name, e2_name = ("e1", "e2") in
    let body =
      mk_op_apply
        ( "Sexplib.Sexp.equal",
          [
            mk_op_apply (sexp_name, [ mkvar e1_name ]);
            mk_op_apply (sexp_name, [ mkvar e2_name ]);
          ] )
    in
    let fv_def = (func_name, [ (e1_name, None); (e2_name, None) ], body) in
    List.map mk_funcdef_args [ fv_def ]
