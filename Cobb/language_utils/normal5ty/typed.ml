module SMTtyped = struct
  include Smtty

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  let map (f : 'a -> 'b) { x; ty } = { x = f x; ty }
  let typed_eq a b = String.equal a.x b.x && eq a.ty b.ty
end

module type T = sig
  include T.T

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  val mk_noty : 'a -> 'a typed
  val ( #: ) : 'a -> t -> 'a typed
  val ( #-> ) : ('a -> 'b) -> 'a typed -> 'b typed
  val layout_typed : ('a -> string) -> 'a typed -> string
  val layout_typed_l : ('a -> string) -> 'a typed list -> string
  val to_smttyped : 'a typed -> 'a SMTtyped.typed
  val typed_eq: string typed -> string typed -> bool
end

module F (Ty : T.T) : T with type t = Ty.t = struct
  include Ty

  type 'a typed = { x : 'a; ty : Ty.t } [@@deriving sexp]

  let ( #: ) x ty = { x; ty }
  let ( #-> ) f { x; ty } = { x = f x; ty }
  let mk_noty x = x #: Ty.default_ty

  (* let xmap f { x; ty } = { x = f x; ty } *)
  let layout_typed f { x; ty } = Printf.sprintf "%s:%s" (f x) (Ty.layout ty)

  let layout_typed_l f l =
    Zzdatatype.Datatype.List.split_by_comma (layout_typed f) l

  let to_smttyped { x; ty } = SMTtyped.{ x; ty = to_smtty ty }
  let typed_eq a b = String.equal a.x b.x && eq a.ty b.ty
end

module Nt = struct
  include Nt

  let layout = Frontend.layout
  let layout_l = Frontend.layout_l
  let layout_coretype = Frontend.layout_
  let of_string = Frontend.of_string
  let _type_unify = __type_unify Frontend.layout
  let _type_unify_ = __type_unify_ Frontend.layout
end

module NotateT = struct
  include Notatet

  let layout x = Frontend.layout (snd x)
  let layout_l x = Frontend.layout_l (List.map snd x)
  let layout_coretype = Frontend.layout_
  let of_string = Frontend.of_string
  let _type_unify _ = failwith "never"
  let _type_unify_ _ = failwith "never"
end

module Ntopt = struct
  include Ntopt

  let layout = function None -> "None" | Some t -> Frontend.layout t
  let layout_l l = Zzdatatype.Datatype.List.split_by_comma layout l
  let layout_coretype = Frontend.layout_
  let of_string = Some Frontend.of_string

  let _type_unify =
    __type_unify (fun x ->
        match x with None -> "None" | Some x -> Frontend.layout x)

  let _type_unify_ =
    __type_unify_ (fun x ->
        match x with None -> "None" | Some x -> Frontend.layout x)
end

module Ntyped = struct
  include F (Nt)
  include Nt
end

module NOpttyped = struct
  include F (Ntopt)
  include Ntopt
end

module Notatedtyped = struct
  include F (NotateT)
  include NotateT
end
