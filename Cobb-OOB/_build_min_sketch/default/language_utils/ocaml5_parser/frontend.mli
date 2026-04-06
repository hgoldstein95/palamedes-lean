# 1 "language_utils/ocaml5_parser/driver/frontend.mli"
val parse: sourcefile:string -> Parsetree.structure
val parse_string: string -> Parsetree.structure
