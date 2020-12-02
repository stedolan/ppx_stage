open Asttypes
open Parsetree
open Ast_helper



type dynamic_modcontext = {
  used_names : (string, unit) Hashtbl.t;
  mods : (int, string * Parsetree.module_expr) Hashtbl.t
}


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
        (f : t -> dynamic_modcontext -> expression)
        (ren : t) (modst : dynamic_modcontext) : expression =
    let entry = Entry { var ; aliases = [] } in
    let vname = variable_name var in
    let shadowed = try IdentMap.find vname ren with Not_found -> [] in
    let result = f (IdentMap.add vname (entry :: shadowed) ren) modst in
    match entry with
    | Entry { var=_; aliases = []} -> result
    | Entry { var=_; aliases } ->
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
    | Pexp_ident { txt = Lident v; loc = _ } ->
       let id () = int_of_string (String.sub v 1 (String.length v - 1)) in
       (match v.[0] with
       | ',' -> f (SubstHole (id ()))
       | ';' -> f (SubstContext (id ()))
       | _ -> pexp)
    | _ -> default_mapper.expr mapper pexp in
  let mapper = { default_mapper with expr } in
  mapper.expr mapper e

let module_remapper f =
  let rename (id : Longident.t Location.loc) : Longident.t Location.loc =
    let rec go : Longident.t -> Longident.t = function
      | Lident id -> Lident (f id)
      | Ldot (id, x) -> Ldot (go id, x)
      | Lapply (idF, idX) -> Lapply (go idF, go idX) in
    {id with txt = go id.txt} in
  let open Parsetree in
  let open Ast_mapper in
  let rec expr mapper pexp =
    let pexp_desc = match pexp.pexp_desc with
      | Pexp_ident id ->
         Pexp_ident (rename id)
      | Pexp_construct (id, e) ->
         Pexp_construct (rename id, expr_opt mapper e)
      | Pexp_record (fs, e) ->
         let fs = List.map (fun (id, e) -> (rename id, expr mapper e)) fs in
         Pexp_record (fs, expr_opt mapper e)
      | Pexp_field (e, f) ->
         Pexp_field (expr mapper e, rename f)
      | Pexp_setfield (e, f, x) ->
         Pexp_setfield (expr mapper e, rename f, expr mapper x)
      | Pexp_new id ->
         Pexp_new (rename id)
      | Pexp_open (md, e) ->
         Pexp_open ({ md with popen_expr = module_expr mapper md.popen_expr },
                    expr mapper e)
      | _ -> (default_mapper.expr mapper pexp).pexp_desc in
    { pexp with pexp_desc }
  and expr_opt mapper = function
    | None -> None
    | Some e -> Some (expr mapper e)
  and typ mapper ptyp =
    let ptyp_desc = match ptyp.ptyp_desc with
      | Ptyp_constr (id, tys) ->
         Ptyp_constr (rename id, List.map (typ mapper) tys)
      | Ptyp_class (id, tys) ->
         Ptyp_class (rename id, List.map (typ mapper) tys)
      | _ -> (default_mapper.typ mapper ptyp).ptyp_desc in
    { ptyp with ptyp_desc }
  and pat mapper ppat =
    let ppat_desc = match ppat.ppat_desc with
      | Ppat_construct (id, pat) ->
         Ppat_construct (rename id, pat_opt mapper pat)
      | Ppat_record (fs, flag) ->
         let fs = List.map (fun (id, p) -> (rename id, pat mapper p)) fs in
         Ppat_record (fs, flag)
      | Ppat_type id ->
         Ppat_type (rename id)
      | Ppat_open (id, p) ->
         Ppat_open (rename id, pat mapper p)
      | _ -> (default_mapper.pat mapper ppat).ppat_desc in
    { ppat with ppat_desc }
  and pat_opt mapper = function
    | None -> None
    | Some p -> Some (pat mapper p)
  and module_type mapper pmty =
    let pmty_desc = match pmty.pmty_desc with
      | Pmty_ident id -> Pmty_ident (rename id)
      | Pmty_alias id -> Pmty_alias (rename id)
      | _ -> (default_mapper.module_type mapper pmty).pmty_desc in
    { pmty with pmty_desc }
  and open_description _mapper op =
    { op with popen_expr = rename op.popen_expr }
  and module_expr mapper pmod =
    let pmod_desc = match pmod.pmod_desc with
      | Pmod_ident id -> Pmod_ident (rename id)
      | _ -> (default_mapper.module_expr mapper pmod).pmod_desc in
    { pmod with pmod_desc }
  in
  { default_mapper with expr; typ; pat; module_type; open_description; module_expr }



module IntMap = Map.Make(struct type t = int let compare = compare end)
module StrMap = Map.Make(struct type t = string let compare = compare end)

type module_code = {
  id : int;
  orig_name : string;
  source : Parsetree.module_expr;
  modcontext : modcontext
}
and modcontext = module_code StrMap.t

let empty_modcontext = StrMap.empty
let max_mod_id = ref 0

let extend_modcontext ctx name source : modcontext =
  incr max_mod_id;
  let md =
    { id = !max_mod_id;
      orig_name = name;
      source;
      modcontext = ctx } in
  StrMap.add name md ctx

let rec rename st (mc : modcontext) (s : string) =
  match StrMap.find s mc with
  | exception Not_found -> s
  | md when Hashtbl.mem st.mods md.id ->
     fst (Hashtbl.find st.mods md.id)
  | md ->
     let freshen name =
       let rec go i =
         let n = name ^ "'" ^ string_of_int i in
         if not (Hashtbl.mem st.used_names n) then
           (Hashtbl.add st.used_names n (); n)
         else
           go (i+1) in
       go 1 in
     let name = freshen md.orig_name in
     let mapper = rename_mapper st md.modcontext in
     let body = mapper.module_expr mapper md.source in
     Hashtbl.add st.mods md.id (name, body);
     name
and rename_mapper st mc = module_remapper (rename st mc)

let rename_modules_in_exp st mc e =
  let mapper = rename_mapper st mc in
  mapper.expr mapper e

let generate_source
    (f : Renaming.t -> dynamic_modcontext -> Parsetree.expression)
    : Parsetree.module_binding list * expression =
  let st = { used_names = Hashtbl.create 20;
             mods = Hashtbl.create 20 } in
  let e = f Renaming.empty st in
  let bindings =
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) st.mods []
    |> List.sort (fun (id, _) (id', _) -> compare id id')
    |> List.map (fun (_id, (name, body)) -> Compat.mk_mb name body) in
  bindings, e

let to_structure (bindings, e) : Parsetree.structure =
  List.map (fun mb -> Str.mk (Pstr_module mb)) bindings @
    [Str.mk (Pstr_value (Nonrecursive, [Vb.mk (Pat.any ()) e]))]
