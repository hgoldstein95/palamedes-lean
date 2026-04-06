module type T = sig
  type t [@@deriving sexp]

  val is_basic_tp : t -> bool
  val is_dt : t -> bool
  val eq : t -> t -> bool
  val destruct_arr_tp : t -> t list * t
  val construct_arr_tp : t list * t -> t
  val mk_arr : t -> t -> t
  val to_smtty : t -> Smtty.t
  val default_ty : t
  val unit_ty : t
  val int_ty : t
  val nat_ty : t
  val bool_ty : t
  val mk_tuple : t list -> t
  val fst_ty : t -> t
  val snd_ty : t -> t
  val get_argty : t -> t
  val get_retty : t -> t
  val layout : t -> string

  val _type_unify_ :
    string ->
    int ->
    t Zzdatatype.Datatype.StrMap.t ->
    t ->
    t ->
    t Zzdatatype.Datatype.StrMap.t * t

  val _type_unify : string -> int -> t -> t -> t
  val mk_record : (string * t) list -> t
  val get_record_types : t -> (string * t) list
end
