type qt = Fa | Ex [@@deriving sexp]
type binary = Implies | Iff [@@deriving sexp]
type multi = And | Or [@@deriving sexp]

let multi_eq a b = match (a, b) with And, And | Or, Or -> true | _ -> false
let is_forall = function Fa -> true | Ex -> false
let is_exists x = not @@ is_forall x

let qt_of_string = function
  | "forall" -> Fa
  | "exists" -> Ex
  | _ -> failwith "not a quantifier"

let qt_to_string = function Fa -> "forall" | Ex -> "exists"
let qt_pretty_layout = function Fa -> "∀ " | Ex -> "∃ "
