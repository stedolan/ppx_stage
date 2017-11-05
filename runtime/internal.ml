open Asttypes
open Parsetree
open Ast_helper


type _ tag = ..
module type T = sig 
  type a
  type _ tag += Tag : a tag
  val name : string
end
type 'a variable = (module T with type a = 'a)

let fresh_variable (type aa) name : aa variable =
  (module struct 
     type a = aa
     type _ tag += Tag : a tag
     let name = name
   end)

let variable_name (type a) ((module V) : a variable) = V.name

type (_, _) cmp_result = Eq : ('a, 'a) cmp_result | NotEq : ('a, 'b) cmp_result
let cmp_variable (type a) (type b) : a variable -> b variable -> (a, b) cmp_result =
  fun (module A) (module B) ->
  match A.Tag with B.Tag -> Eq | _ -> NotEq

let eq_variable (type a) (type b) : a variable -> b variable -> bool =
  fun v1 v2 -> match cmp_variable v1 v2 with Eq -> true | NotEq -> false

module VarMap (C : sig type 'a t end) : sig
  type t
  val empty : t
  val add : t -> 'a variable -> 'a C.t -> t
  val lookup : t -> 'a variable -> 'a C.t option
end = struct
  type entry = Entry : 'b variable * 'b C.t -> entry
  type t = entry list
  let empty = []
  let add m v x = (Entry (v, x) :: m)
  let rec lookup : type a . t -> a variable -> a C.t option =
    fun m v ->
    match m with
    | [] -> None
    | (Entry (v', x')) :: m ->
       match cmp_variable v v' with
       | Eq -> Some x'
       | NotEq -> lookup m v
end

module Environ = VarMap (struct type 'a t = 'a end)

module Renaming = struct

  type entry = Entry : {
      var : 'a variable;
      mutable aliases : IdentMap.ident list
    } -> entry
  type t = entry list IdentMap.t


  let empty = IdentMap.empty

  let with_renaming
        (var : 'a variable)
        (f : t -> expression)
        (ren : t) : expression =
    let entry = Entry { var ; aliases = [] } in
    let vname = variable_name var in
    let shadowed = try IdentMap.find vname ren with Not_found -> [] in
    let result = f (IdentMap.add vname (entry :: shadowed) ren) in
    match entry with
    | Entry { var; aliases = []} -> result
    | Entry { var; aliases } ->
       Exp.let_ Nonrecursive
         (aliases |> List.map (fun alias ->
           Vb.mk
             (Pat.var (Location.mknoloc alias))
             (Exp.ident (Location.mknoloc (Longident.Lident vname)))
         ))
         result

  let lookup (var : 'a variable) (ren : t) =
    let vname = variable_name var in
    let fail () =
      failwith ("Variable " ^ vname ^ " used out of scope") in

    let rec create_alias n =
      let alias = vname ^ "''" ^ string_of_int n in
      if IdentMap.mem alias ren then
        create_alias (n+1)
      else
        alias in

    let rec find_or_create_alias = function
      | [] -> fail ()
      | (Entry ({var = var'; aliases} as entry)) :: _ when eq_variable var var' ->
         (* Even though it was unbound when created, an alias may be shadowed here *)
         begin match List.find (fun v -> not (IdentMap.mem v ren)) aliases with
         | alias ->
            alias
         | exception Not_found ->
            let alias = create_alias 1 in
            entry.aliases <- alias :: aliases;
            alias
         end
      | _ :: rest -> find_or_create_alias rest in

    let bound_name =
      match IdentMap.find vname ren with
      | exception Not_found -> fail ()
      | [] -> assert false
      | (Entry { var = var' ; _ }) :: _ when eq_variable var var' ->
         (* present, not shadowed *)
         vname
      | _ :: shadowed ->
         find_or_create_alias shadowed in
    Exp.ident (Location.mknoloc (Longident.Lident bound_name))
end

let compute_variable v =
  (fun env ->
      match Environ.lookup env v with
      | Some x -> x
      | None ->
         failwith ("Variable " ^ variable_name v ^ " used out of scope"))

let source_variable = Renaming.lookup

open Ast_mapper
type substitutable =
| SubstContext of int
| SubstHole of int

let substitute_holes (e : expression) (f : substitutable -> expression) =
  let expr mapper pexp =
    match pexp.pexp_desc with
    | Pexp_ident { txt = Lident v; loc } ->
       let id () = int_of_string (String.sub v 1 (String.length v - 1)) in
       (match v.[0] with
       | ',' -> f (SubstHole (id ()))
       | ';' -> f (SubstContext (id ()))
       | _ -> pexp)
    | _ -> default_mapper.expr mapper pexp in
  let mapper = { default_mapper with expr } in
  mapper.expr mapper e

