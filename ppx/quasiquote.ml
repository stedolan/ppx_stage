open Migrate_parsetree

open Ast_405

open Asttypes
open Parsetree
open Ast_mapper
open Ast_helper

let mk_ident ?(loc=Location.none) name =
  let rec go = function
    | [] -> failwith "error: mk_ident []"
    | [x] -> Longident.Lident x
    | field :: rest -> Longident.Ldot(go rest, field) in
  { txt = go (List.rev name); loc }

module IM = Ppx_stage.IdentMap

module IntMap = Map.Make (struct type t = int let compare = compare end)

type staged_defs = {
  modname : string;
  mutable def_list : (string * expression) list;
  mutable num_defs : int
}

let add_definition defs exp =
  let id = defs.num_defs in
  defs.num_defs <- id + 1;
  let ident = "staged" ^ string_of_int id in
  defs.def_list <- (ident, exp) :: defs.def_list;
  Exp.ident (mk_ident [defs.modname; ident])

let collect_definitions defs =
  let vbs =
    defs.def_list |> List.rev |> List.map (fun (name, body) -> 
      Vb.mk (Pat.var (Location.mknoloc name)) body) in
  match vbs with
  | [] -> []
  | vbs -> [Str.value Nonrecursive vbs]

(* FIXME: context_vars assumes same names in staged and top program *)
let rec quasiquote staged_defs (context_vars : unit IM.t) loc expr =
  let hole_name h = "hole''_" ^ string_of_int h in

  let context_var_list =
    context_vars
    |> IM.bindings
    |> List.mapi (fun i (name, ()) -> i, name) in

  let context_vars_by_name =
    List.fold_left (fun m (i, name) -> IM.add name i m) IM.empty context_var_list in
  let context_vars_by_id =
    List.fold_left (fun m (i, name) -> IntMap.add i name m) IntMap.empty
      context_var_list in

  let exp_with_holes, hole_table =
    Binding.analyse_binders context_vars_by_name expr in
  let hole_list = Hashtbl.fold (fun k v ks -> k :: ks) hole_table [] |> List.sort compare in

  let binding_site_names =
    Hashtbl.fold (fun _hole (scope, body) acc ->
      IM.fold (fun name site acc ->
        match site with
        | Binding.Binder site when IntMap.mem site acc ->
          (assert (IntMap.find site acc = name); acc)
        | Binding.Binder site ->
          IntMap.add site name acc
        | Binding.Context _ ->
           acc
      ) scope acc
    ) hole_table IntMap.empty in

  let binder_variable_name b =
    let name = IntMap.find b binding_site_names in
    name ^ "''b" ^ string_of_int b in

  let context_variable_name c =
    let name = IntMap.find c context_vars_by_id in
    name ^ "''v" ^ string_of_int c in

  let allocate_variables body =
    IntMap.fold (fun site name body ->
      [%expr let [%p Pat.var (Location.mknoloc (binder_variable_name site))] = Ppx_stage.Internal.fresh_variable [%e Exp.constant (Pconst_string (name, None))] in [%e body]]
      ) binding_site_names body in

  let hole_bindings_list h =
    let scope, body = Hashtbl.find hole_table h in
    IM.fold (fun name site acc -> site :: acc) scope [] in

  let contents_name h =
    "contents''_" ^ string_of_int h in

  let instantiate_holes body =
    List.fold_right (fun hole body ->
      let hole_args =
        hole_bindings_list hole
        |> List.map (function
            | Binding.Context _ -> []
            | Binding.Binder b -> 
               let vare = Exp.ident (mk_ident [binder_variable_name b]) in
               let code = [%expr {
                 Ppx_stage.compute = (fun env -> Ppx_stage.Internal.compute_variable [%e vare] env);
                 Ppx_stage.source = (fun ren -> Ppx_stage.Internal.source_variable [%e vare] ren)
               }] in
               [Nolabel, code])
        |> List.concat in
      let hole_fn = Exp.ident (mk_ident [hole_name hole]) in
      let app = match hole_args with [] -> hole_fn | hole_args -> Exp.apply hole_fn hole_args in
      [%expr let [%p Pat.var (Location.mknoloc (contents_name hole))] = [%e app] in [%e body]]
    ) hole_list body in

  let exp_compute =
    Binding.substitute_holes exp_with_holes (function
    | SubstContext c ->
       (* It is safe to compute context variables in the original
          environment, since by definition they do not depend on
          recent binders *)
       [%expr [%e Exp.ident (mk_ident [context_variable_name c])].Ppx_stage.compute env'']
    | SubstHole h ->
      let env =
        List.fold_left
          (fun env (site : Binding.binding_site) ->
            match site with
            | Context _ ->
             (* already in environment *)
               env
            | Binder b ->
               [%expr Ppx_stage.Internal.Environ.add
                   [%e env]
                   [%e Exp.ident (mk_ident [binder_variable_name b])]
                   [%e Exp.ident (mk_ident [IntMap.find b binding_site_names])]])
          [%expr env'']
          (hole_bindings_list h) in
      [%expr [%e Exp.ident (mk_ident [contents_name h])].Ppx_stage.compute [%e env]]) in


  let exp_source =
    let binary = 
      Versions.((migrate ocaml_405 ocaml_current).copy_expression exp_with_holes)
      |> fun x -> Marshal.to_string x [] in
    let marshalled = Exp.constant (Pconst_string (binary, None)) in
    let pat_int n = Pat.constant (Pconst_integer (string_of_int n, None)) in
    let context_cases = context_var_list |> List.map (fun (c, name) ->
      Exp.case
        (Pat.construct 
           (mk_ident ["Ppx_stage"; "Internal"; "SubstContext"])
           (Some (pat_int c)))
        [%expr [%e Exp.ident (mk_ident [context_variable_name c])].Ppx_stage.source ren'']) in
    let hole_cases = hole_list |> List.map (fun h ->
      let ren = List.fold_left
        (fun exp (site : Binding.binding_site) ->
          match site with
          | Context _ ->
             (* already in environment *)
             exp
          | Binder b ->
             [%expr Ppx_stage.Internal.Renaming.with_renaming
                 [%e Exp.ident (mk_ident [binder_variable_name b])]
                 [%e exp]])
        [%expr [%e Exp.ident (mk_ident [contents_name h])].Ppx_stage.source]
        (hole_bindings_list h) in
      Exp.case
        (Pat.construct
           (mk_ident ["Ppx_stage"; "Internal"; "SubstHole"])
           (Some (pat_int h)))
        [%expr [%e ren] ren'']) in
    let cases =
      context_cases @ hole_cases
      @  [Exp.case (Pat.any ()) [%expr assert false]] in
    [%expr
      Ppx_stage.Internal.substitute_holes
        (Marshal.from_string [%e marshalled] 0)
        [%e Exp.function_ cases]] in


  let staged_code =
    List.fold_right
      (fun (ctx, _) code ->
        [%expr fun [%p Pat.var (Location.mknoloc (context_variable_name ctx))] ->
          [%e code]])
      context_var_list
      (List.fold_right
        (fun hole code ->
          [%expr fun [%p Pat.var (Location.mknoloc (hole_name hole))] -> 
            [%e code]])
        hole_list
        (allocate_variables
           (instantiate_holes
              [%expr { Ppx_stage.compute = (fun env'' -> [%e exp_compute]);
                       Ppx_stage.source = (fun ren'' -> [%e exp_source]) }]))) in

  let staged_code = add_definition staged_defs staged_code in

  let context_contents =
    context_var_list |> List.map (fun (ctx, name) ->
      Nolabel, Exp.ident (mk_ident [name])
    ) in

  let hole_contents =
    hole_list |> List.map (fun hole ->
      let rec gen_hole_body context_vars bindings body =
        match bindings with
        | [] -> quasiquote_subexps staged_defs context_vars body
        | Binding.Context _ :: bindings ->
           (* context variables are already available *)
           gen_hole_body context_vars bindings body
        | Binding.Binder b :: bindings ->
           let name = IntMap.find b binding_site_names in
           gen_hole_body
             (IM.add name () context_vars)
             bindings
             [%expr fun [%p Pat.var (Location.mknoloc name)] -> [%e body]] in
      let (scope, body) = Hashtbl.find hole_table hole in
      Nolabel, gen_hole_body context_vars (List.rev (hole_bindings_list hole)) body) in

  (match context_contents @ hole_contents with
  | [] -> staged_code
  | xs -> Exp.apply staged_code xs)

and quasiquote_mapper staged_defs context_vars =
  let expr mapper pexp =
    match pexp.pexp_desc with
    | Pexp_extension ({ txt = "code"; loc }, code) ->
       begin match code with
       | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
          quasiquote staged_defs context_vars loc e
       | _ ->
          raise (Location.(Error (error ~loc ("[%code] expects an expression"))))
       end
    | Pexp_extension ({ txt = "staged"; loc }, func) ->
       let rec go context_vars e =
         match e.pexp_desc with
         | Pexp_fun (lbl, 
                     opt,
                     ({ ppat_desc = Ppat_var v; _ } as pat),
                     body) ->
            Exp.fun_ ~loc:e.pexp_loc lbl opt pat
                     (go (IM.add v.txt () context_vars) body)
         | Pexp_fun _
         | Pexp_function _ ->
            raise (Location.(Error (error ~loc:e.pexp_loc ("only 'fun v ->' is supported in staged functions"))))
         | _ ->
            quasiquote staged_defs context_vars loc e in
       begin match func with
       | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
          go context_vars e
       | _ ->
          raise (Location.(Error (error ~loc ("fun%staged expects an expression"))))
       end
            
    | _ -> default_mapper.expr mapper pexp in
  { default_mapper with expr }

and quasiquote_subexps staged_defs context_vars exp =
  let mapper = quasiquote_mapper staged_defs context_vars in
  mapper.expr mapper exp

let apply_staging str =
  let initial_defs, str =
    List.partition (fun s -> match s.pstr_desc with
    | Pstr_extension ((id, payload), _) -> id.txt = "code"
    | _ -> false) str in
  let initial_defs = initial_defs
    |> List.map (fun s -> match s.pstr_desc with
      | Pstr_extension (({ txt = "code"; loc }, PStr s), _) -> s
      | _ -> raise Location.(Error (error ~loc:s.pstr_loc ("unsupported contents for [%%code]"))))
    |> List.concat in
  (* Slightly revolting, but we need to avoid Staged being shadowed by things imported from other modules *)
  let modname = "Staged_" ^ string_of_int (Hashtbl.hash str) in
  let staged_defs = { modname; def_list = []; num_defs = 0 } in
  let mapper = quasiquote_mapper staged_defs IM.empty in
  let mapped_str = mapper.structure mapper str in
  let inserted = initial_defs @ collect_definitions staged_defs in
  match inserted, mapped_str with
  | [], mapped_str -> mapped_str
  | inserted, [{pstr_desc = Pstr_eval (e, ats); pstr_loc}] ->
     let e' = Exp.letmodule (Location.mknoloc modname) (Mod.structure inserted) e in
     [{ pstr_desc = Pstr_eval (e', ats); pstr_loc }]
  | inserted, [{pstr_desc = Pstr_value(Nonrecursive, [ vb ]); pstr_loc}] ->
     let e' = Exp.letmodule (Location.mknoloc modname) (Mod.structure inserted) vb.pvb_expr in
     [{ pstr_desc = Pstr_value(Nonrecursive, [ {vb with pvb_expr = e'} ]); pstr_loc}]
  | inserted, mapped_str ->
     Str.module_ (Mb.mk (Location.mknoloc modname) (Mod.structure inserted)) :: mapped_str

let () =
  Driver.register ~name:"ppx_stage" Versions.ocaml_405
    (fun _config _cookies -> make_top_mapper
      ~signature:(fun s -> s)
      ~structure:apply_staging)
