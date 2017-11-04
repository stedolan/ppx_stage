type 'a code = 'a Internal.t

module Internal = Internal
module IdentMap = IdentMap

let print = Internal.print
let run = Internal.run

let source x = Internal.source x Internal.Renaming.empty


module Lift = struct
  open Parsetree
  open Ast_helper

  let lift c p = Internal.Ppx_stage_internal ((fun env -> c), (fun ren -> p))

  let int x : int code =
    lift x (Exp.constant (Pconst_integer (string_of_int x, None)))
  let int32 x : Int32.t code =
    lift x (Exp.constant (Pconst_integer (Int32.to_string x, Some 'l')))
  let int64 x : Int64.t code =
    lift x (Exp.constant (Pconst_integer (Int64.to_string x, Some 'L')))
  let bool x : bool code =
    lift x (Exp.construct (Location.mknoloc (Longident.Lident (string_of_bool x))) None)
  let float x : float code =
    (* OCaml's string_of_float is a bit broken *)
    let s = string_of_float x in
    if float_of_string s = x then
      lift x (Exp.constant (Pconst_float (s, None)))
    else
      lift x (Exp.constant (Pconst_float (Printf.sprintf "%h" x, None)))
  let string x : string code =
    lift x (Exp.constant (Pconst_string (x, None)))
end
