open Ppxlib_ast.Ast
open Ppxlib.Asttypes
open Ppxlib.Ast_builder.Default


type dynamic_modcontext = {
  used_names : (string, unit) Hashtbl.t;
  mods : (int, string * module_expr) Hashtbl.t
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
    let loc = Location.none in
    let entry = Entry { var ; aliases = [] } in
    let vname = variable_name var in
    let shadowed = try IdentMap.find vname ren with Not_found -> [] in
    let result = f (IdentMap.add vname (entry :: shadowed) ren) modst in
    match entry with
    | Entry { var=_; aliases = []} -> result
    | Entry { var=_; aliases } ->
       pexp_let
         ~loc
         Nonrecursive
         (aliases |> List.map (fun alias ->
           value_binding
             ~loc
             ~pat:(pvar ~loc alias)
             ~expr:(evar ~loc vname)
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
    evar ~loc:Location.none bound_name
end

let compute_variable v =
  (fun env ->
      match Environ.lookup env v with
      | Some x -> x
      | None ->
         failwith ("Variable " ^ variable_name v ^ " used out of scope"))

let source_variable = Renaming.lookup

type substitutable =
| SubstContext of int
| SubstHole of int

let substitute_holes (e : expression) (f : substitutable -> expression) =
  let mapper =
    object
      inherit Ppxlib.Ast_traverse.map as super

      method! expression pexp =
        match pexp.pexp_desc with
        | Pexp_ident { txt = Lident v; loc = _ } ->
           let id () = int_of_string (String.sub v 1 (String.length v - 1)) in
           (match v.[0] with
           | ',' -> f (SubstHole (id ()))
           | ';' -> f (SubstContext (id ()))
           | _ -> pexp)
        | _ -> super#expression pexp
    end
  in
  mapper#expression e

let module_remapper f =
  let rename (id : Longident.t Location.loc) : Longident.t Location.loc =
    let rec go : Longident.t -> Longident.t = function
      | Lident id -> Lident (f id)
      | Ldot (id, x) -> Ldot (go id, x)
      | Lapply (idF, idX) -> Lapply (go idF, go idX) in
    {id with txt = go id.txt} in
  object (self)
    inherit Ppxlib.Ast_traverse.map as super

    method expression_opt = function
      | None -> None
      | Some e -> Some (self#expression e)

    method! expression pexp =
      let pexp_desc = match pexp.pexp_desc with
        | Pexp_ident id ->
            Pexp_ident (rename id)
        | Pexp_construct (id, e) ->
            Pexp_construct (rename id, self#expression_opt e)
        | Pexp_record (fs, e) ->
            let fs = List.map (fun (id, e) -> (rename id, self#expression e)) fs in
            Pexp_record (fs, self#expression_opt e)
        | Pexp_field (e, f) ->
            Pexp_field (self#expression e, rename f)
        | Pexp_setfield (e, f, x) ->
            Pexp_setfield (self#expression e, rename f, self#expression x)
        | Pexp_new id ->
            Pexp_new (rename id)
        | Pexp_open (md, e) ->
            Pexp_open ({ md with popen_expr = self#module_expr md.popen_expr },
                      self#expression e)
        | _ -> (super#expression pexp).pexp_desc in
      { pexp with pexp_desc }

    method! core_type ptyp =
      let ptyp_desc = match ptyp.ptyp_desc with
        | Ptyp_constr (id, tys) ->
            Ptyp_constr (rename id, List.map (self#core_type) tys)
        | Ptyp_class (id, tys) ->
            Ptyp_class (rename id, List.map (self#core_type) tys)
        | _ -> (super#core_type ptyp).ptyp_desc in
      { ptyp with ptyp_desc }

    method! pattern ppat =
      let ppat_desc = match ppat.ppat_desc with
        | Ppat_construct (id, pat) ->
            Ppat_construct (rename id, self#pattern_opt pat)
        | Ppat_record (fs, flag) ->
            let fs = List.map (fun (id, p) -> (rename id, self#pattern p)) fs in
            Ppat_record (fs, flag)
        | Ppat_type id ->
            Ppat_type (rename id)
        | Ppat_open (id, p) ->
            Ppat_open (rename id, self#pattern p)
        | _ -> (super#pattern ppat).ppat_desc in
      { ppat with ppat_desc }

    method pattern_opt = function
      | None -> None
      | Some (locs, p) -> Some (locs, self#pattern p)

    method! module_type pmty =
      let pmty_desc = match pmty.pmty_desc with
        | Pmty_ident id -> Pmty_ident (rename id)
        | Pmty_alias id -> Pmty_alias (rename id)
        | _ -> (super#module_type pmty).pmty_desc in
      { pmty with pmty_desc }

    method! open_description op =
      { op with popen_expr = rename op.popen_expr }

    method! module_expr pmod =
      let pmod_desc = match pmod.pmod_desc with
        | Pmod_ident id -> Pmod_ident (rename id)
        | _ -> (super#module_expr pmod).pmod_desc in
      { pmod with pmod_desc }
  end



module IntMap = Map.Make(struct type t = int let compare = compare end)
module StrMap = Map.Make(struct type t = string let compare = compare end)

type module_code = {
  id : int;
  orig_name : string;
  source : module_expr;
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
     let body = mapper#module_expr md.source in
     Hashtbl.add st.mods md.id (name, body);
     name
and rename_mapper st mc = module_remapper (rename st mc)

let rename_modules_in_exp st mc e =
  let mapper = rename_mapper st mc in
  mapper#expression e

let generate_source
    (f : Renaming.t -> dynamic_modcontext -> expression)
    : module_binding list * expression =
  let st = { used_names = Hashtbl.create 20;
             mods = Hashtbl.create 20 } in
  let e = f Renaming.empty st in
  let bindings =
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) st.mods []
    |> List.sort (fun (id, _) (id', _) -> compare id id')
    |> List.map (fun (_id, (name, body)) -> module_binding ~loc:Location.none ~name:(Location.mkloc (Some name) Location.none) ~expr:body) in
  bindings, e

let to_structure (bindings, e) : structure =
  let loc = Location.none in
  List.map (fun mb -> pstr_module ~loc mb) bindings @
    [pstr_value ~loc Nonrecursive [value_binding ~loc ~pat:(ppat_any ~loc) ~expr:e]]
