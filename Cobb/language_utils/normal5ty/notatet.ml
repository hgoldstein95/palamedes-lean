open Sexplib.Std
(* open Sugar *)

type t = string option * Nt.t [@@deriving sexp]

let eq (a1, b1) (a2, b2) =
  match (a1, a2) with
  | None, None -> Nt.eq b1 b2
  | Some a1, Some a2 when String.equal a1 a2 -> Nt.eq b1 b2
  | _ -> false

let is_basic_tp _ = failwith "notatet never"
let is_dt _ = failwith "notatet never"
let fst_ty _ = failwith "notatet never"
let snd_ty _ = failwith "notatet never"
let destruct_arr_tp _ = failwith "notatet never"
let construct_arr_tp _ = failwith "notatet never"
let to_smtty _ = failwith "notatet never"
let default_ty = (None, Nt.Ty_unknown)
let unit_ty = default_ty
let int_ty = default_ty
let nat_ty = default_ty
let bool_ty = default_ty
let uninter_ty _ = failwith "notatet never"
let mk_arr _ = failwith "notatet never"
let mk_tuple _ = failwith "notatet never"
let mk_record _ = failwith "notatet never"
let get_record_types _ = failwith "notatet never"
let get_argty _ = failwith "notatet never"
let get_retty _ = failwith "notatet never"
let subst _ = failwith "notatet never"
let subst_m _ = failwith "notatet never"
let layout _ = failwith "notatet never"
let __type_unify_ _ = failwith "notatet never"
let __type_unify _ = failwith "notatet never"
