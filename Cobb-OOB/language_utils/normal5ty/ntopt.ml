open Sexplib.Std
open Sugar

type t = Nt.t option [@@deriving sexp]

let is_basic_tp = function
  | Some t -> Nt.is_basic_tp t
  | None -> _failatwith __FILE__ __LINE__ "?"

let is_dt = function
  | Some t -> Nt.is_dt t
  | None -> _failatwith __FILE__ __LINE__ "?"

let eq x y =
  match (x, y) with
  | None, None -> true
  | Some x, Some y -> Nt.eq x y
  | _, _ -> false

let destruct_arr_tp = function
  | Some t ->
      let t1, t2 = Nt.destruct_arr_tp t in
      (List.map (fun x -> Some x) t1, Some t2)
  | None -> _failatwith __FILE__ __LINE__ "?"

let construct_arr_tp (t1, t2) =
  let t1 =
    List.map
      (fun x ->
        match x with None -> _failatwith __FILE__ __LINE__ "?" | Some x -> x)
      t1
  in
  match t2 with
  | Some t2 -> Some (Nt.construct_arr_tp (t1, t2))
  | _ -> _failatwith __FILE__ __LINE__ "?"

let to_smtty = function
  | Some t -> Nt.to_smtty t
  | None -> _failatwith __FILE__ __LINE__ "?"

let default_ty = None
let unit_ty = Some Nt.Ty_unit
let int_ty = Some Nt.Ty_int
let nat_ty = Some Nt.Ty_nat
let bool_ty = Some Nt.Ty_bool

let mk_arr t1 t2 =
  match (t1, t2) with
  | Some t1, Some t2 -> Some (Nt.Ty_arrow (t1, t2))
  | _, _ -> None

let mk_tuple ts =
  let* ts = Sugar.opt_list_to_list_opt ts in
  Some (Nt.mk_tuple ts)

let fst_ty = function None -> None | Some ty -> Some (Nt.fst_ty ty)
let snd_ty = function None -> None | Some ty -> Some (Nt.snd_ty ty)

let get_argty = function
  | Some (Nt.Ty_arrow (t1, _)) -> Some t1
  | _ -> _failatwith __FILE__ __LINE__ "?"

let get_retty = function
  | Some (Nt.Ty_arrow (_, t2)) -> Some t2
  | _ -> _failatwith __FILE__ __LINE__ "?"

let layout = function None -> "None" | Some t -> Nt.layout t

let __type_unify pprint file line t1 t2 =
  let pprint x = pprint (Some x) in
  match (t1, t2) with
  | Some t1, Some t2 -> Some (Nt.__type_unify pprint file line t1 t2)
  | Some t1, None -> Some t1
  | None, t2 -> t2

let __type_unify_ pprint file line s t1 t2 =
  let pprint x = pprint (Some x) in
  let s' =
    Zzdatatype.Datatype.StrMap.map
      (fun x ->
        match x with None -> _failatwith __FILE__ __LINE__ "die" | Some x -> x)
      s
  in
  match (t1, t2) with
  | Some t1, Some t2 ->
      let s, t = Nt.__type_unify_ pprint file line s' t1 t2 in
      let s = Zzdatatype.Datatype.StrMap.map (fun x -> Some x) s in
      (s, Some t)
  | Some t1, None -> (s, Some t1)
  | None, t2 -> (s, t2)

let get_record_types = function
  | Some (Nt.Ty_record l) -> List.map (fun (x, t) -> (x, Some t)) l
  | _ -> _failatwith __FILE__ __LINE__ "die"

let mk_record ts =
  let* ts =
    List.fold_right
      (fun (x, t) res ->
        let* l = res in
        let* t = t in
        Some ((x, t) :: l))
      ts (Some [])
  in
  Some (Nt.Ty_record ts)
