let ocaml_version = "5.0.1+dev0-2022-12-15"

let development_version = true

type extra_prefix = Plus | Tilde

type extra_info = extra_prefix * string

type ocaml_release_info = {
  major : int;
  minor : int;
  patchlevel : int;
  extra : extra_info option
}

let ocaml_release = {
  major = 5;
  minor = 0;
  patchlevel = 1;
  extra = Some (Plus, "dev0-2022-12-15")
}
