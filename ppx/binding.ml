open Migrate_parsetree
open Ast_405

open Asttypes
open Parsetree
open Ast_helper

type binding_site = Binder of int | Context of int

module IdentMap = Ppx_stage.IdentMap
type scope = binding_site IdentMap.t

type hole = int

type analysis_env = {
  bindings : scope;
  fresh_binder : unit -> binding_site;
  fresh_hole : unit -> hole;
  hole_table : (hole, scope * expression) Hashtbl.t
}

let rec analyse_exp env { pexp_desc; pexp_loc; pexp_attributes } =
  analyse_attributes pexp_attributes;
  { pexp_desc = analyse_exp_desc env pexp_loc pexp_desc;
    pexp_loc;
    pexp_attributes }

and analyse_exp_desc env loc = function
  | Pexp_extension ({txt = "e"; loc}, code) ->
     let code =
       match code with
       | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
          e
       | _ ->
          raise (Location.(Error (error ~loc ("[%e] expects an expression")))) in
     let h = env.fresh_hole () in
     Hashtbl.add env.hole_table h (env.bindings, code);
     Pexp_ident { txt = Lident ("," ^ string_of_int h); loc }
  | Pexp_ident { txt = Lident id; loc } as e ->
     begin match IdentMap.find id env.bindings with
     | Context c ->
        Pexp_ident { txt = Lident (";" ^ string_of_int c); loc }
     | Binder _ -> e
     | exception Not_found -> e
     end
  | Pexp_ident { txt = (Ldot _ | Lapply _); _ } as e -> e
  | Pexp_constant _ as e -> e
  | Pexp_let (isrec, vbs, body) ->
     let env' = List.fold_left (fun env {pvb_pat; _} ->
       analyse_pat env pvb_pat) env vbs in
     let bindings_env =
       match isrec with Recursive -> env' | Nonrecursive -> env in
     Pexp_let
       (isrec,
        vbs |> List.map (fun vb ->
          analyse_attributes vb.pvb_attributes;
          { vb with pvb_expr = analyse_exp bindings_env vb.pvb_expr }),
        analyse_exp env' body)
  | Pexp_function cases ->
     Pexp_function (List.map (analyse_case env) cases)
  | Pexp_fun (lbl, opt, pat, body) ->
     let env' = analyse_pat env pat in
     Pexp_fun (lbl, analyse_exp_opt env opt, pat, analyse_exp env' body)
  | Pexp_apply (fn, args) ->
     Pexp_apply
       (analyse_exp env fn,
        args |> List.map (fun (lbl, e) -> lbl, analyse_exp env e))
  | Pexp_match (exp, cases) ->
     Pexp_match
       (analyse_exp env exp,
        List.map (analyse_case env) cases)
  | Pexp_try (exp, cases) ->
     Pexp_try
       (analyse_exp env exp,
        List.map (analyse_case env) cases)
  | Pexp_tuple exps ->
     Pexp_tuple (List.map (analyse_exp env) exps)
  | Pexp_construct (ctor, exp) ->
     Pexp_construct (ctor, analyse_exp_opt env exp)
  | Pexp_variant (lbl, exp) ->
     Pexp_variant (lbl, analyse_exp_opt env exp)
  | Pexp_record (fields, base) ->
     Pexp_record (List.map (fun (l, e) -> l, analyse_exp env e) fields, analyse_exp_opt env base)
  | Pexp_field (e, field) ->
     Pexp_field (analyse_exp env e, field)
  | Pexp_setfield (e, field, v) ->
     Pexp_setfield (analyse_exp env e, field, analyse_exp env v)
  | Pexp_array exps ->
     Pexp_array (List.map (analyse_exp env) exps)
  | Pexp_ifthenelse (cond, ift, iff) ->
     Pexp_ifthenelse (analyse_exp env cond, analyse_exp env ift, analyse_exp_opt env iff)
  | Pexp_sequence (e1, e2) ->
     Pexp_sequence (analyse_exp env e1, analyse_exp env e2)
  | Pexp_while (cond, body) ->
     Pexp_while (analyse_exp env cond, analyse_exp env body)
  | Pexp_for (pat, e1, e2, dir, body) ->
     let env' = analyse_pat env pat in
     Pexp_for (pat, analyse_exp env e1, analyse_exp env e2, dir, analyse_exp env' body)
  (* several missing... *)
       

  | _ -> raise (Location.(Error (error ~loc ("expression not supported in staged code"))))

and analyse_exp_opt env = function
  | None -> None
  | Some e -> Some (analyse_exp env e)

and analyse_pat env { ppat_desc; ppat_loc; ppat_attributes } =
  analyse_attributes ppat_attributes;
  analyse_pat_desc env ppat_loc ppat_desc

and analyse_pat_desc env loc = function
  | Ppat_any -> env
  | Ppat_var v -> analyse_pat_desc env loc (Ppat_alias (Pat.any (), v))
  | Ppat_alias (pat, v) ->
     let env = analyse_pat env pat in
     { env with bindings = IdentMap.add v.txt (env.fresh_binder ()) env.bindings }
  | Ppat_constant _ -> env
  | Ppat_interval _ -> env
  | Ppat_tuple pats -> List.fold_left analyse_pat env pats
  | Ppat_construct (loc, None) -> env
  | Ppat_construct (loc, Some pat) -> analyse_pat env pat
  | _ -> raise (Location.(Error (error ~loc ("pattern not supported in staged code"))))

and analyse_case env {pc_lhs; pc_guard; pc_rhs} =
  let env' = analyse_pat env pc_lhs in
  { pc_lhs;
    pc_guard = analyse_exp_opt env' pc_guard;
    pc_rhs = analyse_exp env' pc_rhs }

and analyse_attributes = function
| [] -> ()
| ({ loc; txt }, PStr []) :: rest ->
   analyse_attributes rest
| ({ loc; txt }, _) :: _ ->
   raise (Location.(Error (error ~loc ("attribute " ^ txt ^ " not supported in staged code"))))


let analyse_binders (context : int IdentMap.t) (e : expression) :
    expression * (hole, scope * expression) Hashtbl.t =
  let hole_table = Hashtbl.create 20 in
  let next_hole = ref 0 in
  let fresh_hole () =
    incr next_hole;
    !next_hole in
  let next_binder = ref 0 in
  let fresh_binder () =
    incr next_binder;
    Binder (!next_binder) in
  let bindings = IdentMap.map (fun c -> Context c) context in
  let e' = analyse_exp { bindings; fresh_binder; fresh_hole; hole_table } e in
  e', hole_table



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
      | Pexp_open (flag, id, e) ->
         Pexp_open (flag, rename id, expr mapper e)
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
  and open_description mapper op =
    { op with popen_lid = rename op.popen_lid }
  and module_expr mapper pmod =
    let pmod_desc = match pmod.pmod_desc with
      | Pmod_ident id -> Pmod_ident (rename id)
      | _ -> (default_mapper.module_expr mapper pmod).pmod_desc in
    { pmod with pmod_desc }
  in
  { default_mapper with expr; typ; pat; module_type; open_description; module_expr }
