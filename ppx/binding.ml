open Ppxlib
open Ppxlib.Ast_builder.Default

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

let rec analyse_exp env exp =
  analyse_attributes exp.pexp_attributes;
  { exp with pexp_desc = analyse_exp_desc env exp.pexp_loc exp.pexp_desc }

and analyse_exp_desc env loc = function
  | Pexp_extension ({txt = "e"; loc}, code) ->
     let code =
       match code with
       | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
          e
       | _ ->
         raise (Location.(Error (Error.make ~sub:[] ~loc ("[%e] expects an expression")))) in
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

  | _ -> raise (Location.(Error (Error.make ~sub:[] ~loc ("expression not supported in staged code"))))

and analyse_exp_opt env = function
  | None -> None
  | Some e -> Some (analyse_exp env e)

and analyse_pat env pat =
  analyse_attributes pat.ppat_attributes;
  analyse_pat_desc env pat.ppat_loc pat.ppat_desc

and analyse_pat_desc env loc = function
  | Ppat_any -> env
  | Ppat_var v -> analyse_pat_desc env loc (Ppat_alias (ppat_any ~loc, v))
  | Ppat_alias (pat, v) ->
     let env = analyse_pat env pat in
     { env with bindings = IdentMap.add v.txt (env.fresh_binder ()) env.bindings }
  | Ppat_constant _ -> env
  | Ppat_interval _ -> env
  | Ppat_tuple pats -> List.fold_left analyse_pat env pats
  | Ppat_construct (_loc, None) -> env
  | Ppat_construct (_loc, Some (_locs, pat)) -> analyse_pat env pat
  | _ -> raise (Location.(Error (Error.make ~sub:[] ~loc ("pattern not supported in staged code"))))

and analyse_case env {pc_lhs; pc_guard; pc_rhs} =
  let env' = analyse_pat env pc_lhs in
  { pc_lhs;
    pc_guard = analyse_exp_opt env' pc_guard;
    pc_rhs = analyse_exp env' pc_rhs }

and analyse_attributes = function
| [] -> ()
| {attr_payload=PStr []; _} :: rest ->
   analyse_attributes rest
| {attr_name={loc;txt}; _} :: _ ->
    raise (Location.(Error (Error.make ~sub:[] ~loc ("attribute " ^ txt ^ " not supported in staged code"))))


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


let module_remapper = Ppx_stage.Internal.module_remapper
