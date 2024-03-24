module Internal = Internal
module IdentMap = IdentMap

type 'a code = {
  compute : Internal.Environ.t -> 'a;
  source : Internal.Renaming.t -> Internal.dynamic_modcontext -> Ppxlib.expression;
}

let to_parsetree_structure f =
  Internal.generate_source f.source
  |> Internal.to_structure

(* let to_parsetree f = f.source Internal.Renaming.empty *)

let run f = f.compute Internal.Environ.empty

let print ppf f =
  Astlib.Pprintast.structure ppf (to_parsetree_structure f)



module Lift = struct
  open Ppxlib
  open Ppxlib.Ast_builder.Default

  let lift c p = { compute = (fun _env -> c); source = (fun _ren _modst -> p) }

  let int x : int code =
    lift x (eint ~loc:Location.none x)
  let int32 x : Int32.t code =
    lift x (eint32 ~loc:Location.none x)
  let int64 x : Int64.t code =
    lift x (eint64 ~loc:Location.none x)
  let bool x : bool code =
    lift x (ebool ~loc:Location.none x)
  let float x : float code =
    (* OCaml's string_of_float is a bit broken *)
    let s = string_of_float x in
    if float_of_string s = x then
      lift x (efloat ~loc:Location.none s)
    else
      lift x (efloat ~loc:Location.none (Printf.sprintf "%h" x))
  let string x : string code =
    lift x (estring ~loc:Location.none x)
end


type staged_module = Ppxlib.Parsetree.module_expr
