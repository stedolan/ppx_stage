open Parsetree
open Ast_helper

let mk_mb name body =
#if OCAML_VERSION < (4, 10, 0)
  Mb.mk (Location.mknoloc name) body
#else
  Mb.mk (Location.mknoloc (Some name)) body
#endif

let pconst_string x =
#if OCAML_VERSION < (4, 11, 0)
  Pconst_string (x, None)
#else
  Pconst_string (x, Location.none, None)
#endif
