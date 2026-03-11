# 1 "language_utils/ocaml5_parser/stdlib/zint.ml"
type t = int
let min x y : t = if x <= y then x else y
let max x y : t = if x >= y then x else y
