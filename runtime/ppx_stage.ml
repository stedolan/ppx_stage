module Internal = Internal
module IdentMap = IdentMap

type 'a code = {
  compute : Internal.Environ.t -> 'a;
  source : Internal.Renaming.t -> Parsetree.expression
}

let to_parsetree f = f.source Internal.Renaming.empty

let run f = f.compute Internal.Environ.empty

let print ppf f =
  Pprintast.expression ppf (to_parsetree f)



module Lift = struct
  open Parsetree
  open Ast_helper

  let lift c p = { compute = (fun env -> c); source = (fun ren -> p) }

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


type staged_module = Parsetree.structure


type mod_identifier = int
module ModMap = Map.Make (struct type t = mod_identifier let compare = compare end)
