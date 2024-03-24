open Ppxlib
open Ppxlib.Ast_builder.Default

let mk_ident ?(loc=Location.none) name =
  let rec go = function
    | [] -> failwith "error: mk_ident []"
    | [x] -> Longident.Lident x
    | field :: rest -> Longident.Ldot(go rest, field) in
  { txt = go (List.rev name); loc }

module IM = Ppx_stage.IdentMap

module IntMap = Map.Make (struct type t = int let compare = compare end)

module StrMap = Map.Make (struct type t = string let compare = compare end)

type staged_defs = {
  modname : Longident.t;
  mutable def_list : structure_item list;
  mutable num_defs : int
}

let make_module_renamer names =
  Binding.module_remapper (fun s ->
      match StrMap.find s names with
      | s' -> s'
      | exception Not_found -> s)

let rename_module names mexp =
  let m = make_module_renamer names in
  m#module_expr mexp

let add_structure_item defs s =
  defs.num_defs <- defs.num_defs + 1;
  defs.def_list <- s :: defs.def_list

let add_definition defs expr =
  let loc = Location.none in
  let id = defs.num_defs in
  defs.num_defs <- id + 1;
  let ident = "staged" ^ string_of_int id in
  let def = pstr_value ~loc Nonrecursive [value_binding ~loc ~pat:(pvar ~loc ident) ~expr] in
  defs.def_list <- def :: defs.def_list;
  pexp_ident ~loc (Located.mk ~loc (Longident.Ldot (defs.modname, ident)))

let add_defmodule defs (pmod : module_expr) : Parsetree.module_expr =
  let loc = Location.none in
  let id = defs.num_defs in
  defs.num_defs <- id + 1;
  let ident = "Staged_" ^ string_of_int id in
  let ident' = Located.mk ~loc (Some ident) in
  let def = pstr_module ~loc (module_binding ~loc ~name:ident' ~expr:pmod) in
  defs.def_list <- def :: defs.def_list;
  pmod_ident ~loc (Located.mk ~loc (Longident.Ldot (defs.modname, ident)))

let collect_definitions defs =
  List.rev defs.def_list

(* FIXME: context_vars assumes same names in staged and top program *)
let rec quasiquote staged_defs modrenamer (context_vars : unit IM.t) _loc expr =
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
  let hole_list = Hashtbl.fold (fun k _v ks -> k :: ks) hole_table [] |> List.sort compare in

  let binding_site_names =
    Hashtbl.fold (fun _hole (scope, _body) acc ->
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
    let loc = Location.none in
    IntMap.fold (fun site name body ->
      [%expr
        let [%p pvar ~loc (binder_variable_name site)] =
          Ppx_stage.Internal.fresh_variable [%e estring ~loc name]
        in [%e body]]
      ) binding_site_names body in

  let hole_bindings_list h =
    let scope, _body = Hashtbl.find hole_table h in
    IM.fold (fun _name site acc -> site :: acc) scope [] in

  let contents_name h =
    "contents''_" ^ string_of_int h in

  let instantiate_holes body =
    let loc = Location.none in
    List.fold_right (fun hole body ->
      let hole_args =
        hole_bindings_list hole
        |> List.map (function
            | Binding.Context _ -> []
            | Binding.Binder b ->
               let vare = pexp_ident ~loc (mk_ident [binder_variable_name b]) in
               let code = [%expr {
                 Ppx_stage.compute = (fun env -> Ppx_stage.Internal.compute_variable [%e vare] env);
                 Ppx_stage.source = (fun ren modst -> Ppx_stage.Internal.source_variable [%e vare] ren)
               }] in
               [code])
        |> List.concat in
      let hole_fn = pexp_ident ~loc (mk_ident [hole_name hole]) in
      let app = match hole_args with [] -> hole_fn | hole_args -> eapply ~loc hole_fn hole_args in
      [%expr let [%p pvar ~loc (contents_name hole)] = [%e app] in [%e body]]
    ) hole_list body in

  let exp_compute =
    let loc = Location.none in
    Ppx_stage.Internal.substitute_holes exp_with_holes (function
    | SubstContext c ->
       (* It is safe to compute context variables in the original
          environment, since by definition they do not depend on
          recent binders *)
       [%expr [%e pexp_ident ~loc (mk_ident [context_variable_name c])].Ppx_stage.compute env'']
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
                   [%e pexp_ident ~loc (mk_ident [binder_variable_name b])]
                   [%e pexp_ident ~loc (mk_ident [IntMap.find b binding_site_names])]])
          [%expr env'']
          (hole_bindings_list h) in
      [%expr [%e pexp_ident ~loc (mk_ident [contents_name h])].Ppx_stage.compute [%e env]]) in


  let exp_source =
    let loc = Location.none in
    let binary =
      (exp_with_holes : Ppxlib.expression) |> fun x -> Marshal.to_string x [] in
    let marshalled = estring ~loc binary in
    let context_cases = context_var_list |> List.map (fun (c, _name) ->
      case
        ~lhs:(ppat_construct
          ~loc
          (mk_ident ["Ppx_stage"; "Internal"; "SubstContext"])
          (Some (pint ~loc c)))
        ~guard:None
        ~rhs:[%expr [%e pexp_ident ~loc (mk_ident [context_variable_name c])].Ppx_stage.source ren'' modst'']) in
    let hole_cases = hole_list |> List.map (fun h ->
      let ren = List.fold_left
        (fun exp (site : Binding.binding_site) ->
          match site with
          | Context _ ->
             (* already in environment *)
             exp
          | Binder b ->
             [%expr Ppx_stage.Internal.Renaming.with_renaming
                 [%e pexp_ident ~loc (mk_ident [binder_variable_name b])]
                 [%e exp]])
        [%expr [%e pexp_ident ~loc (mk_ident [contents_name h])].Ppx_stage.source]
        (hole_bindings_list h) in
      case
        ~lhs:(ppat_construct
          ~loc
          (mk_ident ["Ppx_stage"; "Internal"; "SubstHole"])
          (Some (pint ~loc h)))
        ~guard:None
        ~rhs:[%expr [%e ren] ren'' modst'']) in
    let cases =
      context_cases @ hole_cases
      @  [case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:[%expr assert false]] in
    [%expr
      Ppx_stage.Internal.substitute_holes
        (Ppx_stage.Internal.rename_modules_in_exp modst'' modcontext''_
           (Marshal.from_string [%e marshalled] 0))
        [%e pexp_function ~loc cases]] in


  let staged_code =
    let loc = Location.none in
    List.fold_right
      (fun (ctx, _) code ->
        [%expr fun [%p pvar ~loc (context_variable_name ctx)] ->
          [%e code]])
      context_var_list
      (List.fold_right
        (fun hole code ->
          [%expr fun [%p pvar ~loc (hole_name hole)] ->
            [%e code]])
        hole_list
        (allocate_variables
           (instantiate_holes
              [%expr { Ppx_stage.compute = (fun env'' -> [%e exp_compute]);
                       Ppx_stage.source = (fun ren'' modst'' -> [%e exp_source]) }]))) in

  let staged_code = add_definition staged_defs (modrenamer#expression staged_code) in

  let context_contents =
    context_var_list |> List.map (fun (_ctx, name) ->
      Nolabel, evar ~loc:Location.none name
    ) in

  let hole_contents =
    let loc = Location.none in
    hole_list |> List.map (fun hole ->
      let rec gen_hole_body context_vars bindings body =
        match bindings with
        | [] -> quasiquote_subexps staged_defs modrenamer context_vars body
        | Binding.Context _ :: bindings ->
           (* context variables are already available *)
           gen_hole_body context_vars bindings body
        | Binding.Binder b :: bindings ->
           let name = IntMap.find b binding_site_names in
           gen_hole_body
             (IM.add name () context_vars)
             bindings
             [%expr fun [%p pvar ~loc name] -> [%e body]] in
      let (_scope, body) = Hashtbl.find hole_table hole in
      Nolabel, gen_hole_body context_vars (List.rev (hole_bindings_list hole)) body) in

  (match context_contents @ hole_contents with
  | [] -> staged_code
  | xs -> pexp_apply ~loc:Location.none staged_code xs)

and quasiquote_mapper staged_defs modrenamer context_vars =
  object
    inherit Ppxlib.Ast_traverse.map as super

    method! expression pexp =
      match pexp.pexp_desc with
      | Pexp_extension ({ txt = "code"; loc }, code) ->
         begin match code with
         | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
            quasiquote staged_defs modrenamer context_vars loc e
         | _ ->
           raise (Location.(Error (Error.make ~sub:[] ~loc ("[%code] expects an expression"))))
         end
      | Pexp_extension ({ txt = "staged"; loc }, func) ->
         let rec go context_vars e =
           match e.pexp_desc with
           | Pexp_fun (lbl,
                       opt,
                       ({ ppat_desc = Ppat_var v; _ } as pat),
                       body) ->
              pexp_fun ~loc:e.pexp_loc lbl opt pat
                       (go (IM.add v.txt () context_vars) body)
           | Pexp_fun _
           | Pexp_function _ ->
             raise (Location.(Error (Error.make ~sub:[] ~loc:e.pexp_loc ("only 'fun v ->' is supported in staged functions"))))
           | _ ->
              quasiquote staged_defs modrenamer context_vars loc e in
         begin match func with
         | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
            go context_vars e
         | _ ->
           raise (Location.(Error (Error.make ~sub:[] ~loc ("fun%staged expects an expression"))))
         end
      | _ -> super#expression pexp

    method! module_expr =
      let loc = Location.none in
      function
      (* FIXME: support signatures here *)
      | {pmod_attributes = [{attr_name={txt = "code"; _};_}]; _} as pmod ->
         let pmod = { pmod with pmod_attributes = [] } in
         let marshalled =
           estring ~loc (Marshal.to_string (pmod : module_expr) []) in
         add_defmodule staged_defs {pmod with
           pmod_attributes = [];
           pmod_desc = Pmod_structure (
             (pstr_module ~loc
               (module_binding ~loc ~name:(Located.mk ~loc (Some "Staged_module"))
                                    ~expr:(modrenamer#module_expr pmod)))
             :: [%str
             let staged_source : Ppx_stage.staged_module =
               Marshal.from_string [%e marshalled] 0])}
      | pmod -> super#module_expr pmod

    method! module_type =
      let loc = Location.none in
      function
      | {pmty_attributes = [{attr_name={txt = "code"; _}; _}]; _} as pmty ->
         {pmty with pmty_attributes = []; pmty_desc = Pmty_signature [
           psig_module
             ~loc
             (module_declaration
               ~loc
               ~name:(Located.mk ~loc (Some "Staged_module"))
               ~type_:(modrenamer#module_type pmty));
           [%sigi: val staged_source : Ppx_stage.staged_module]
           ]}
      | pmty -> super#module_type pmty
  end

and quasiquote_subexps staged_defs modrenamer context_vars exp =
  let mapper = quasiquote_mapper staged_defs modrenamer context_vars in
  mapper#expression exp



(* module%code and functors *)
let rec quasiquote_structure
          staged_defs
          functor_arg_names
          module_code_names
          str =
  let mapper = quasiquote_mapper staged_defs (make_module_renamer module_code_names) IM.empty in
  match str with
  | [] -> []
  | stri :: rest ->
    match stri.pstr_desc with
    | Pstr_extension (({txt = "code"; _}, PStr [{pstr_desc = (Pstr_module mb); _}]), _) ->
       let staged_modname = Option.get mb.pmb_name.txt ^ "_StagedCode_" in
       let loc = mb.pmb_loc in
       let mexp = mapper#module_expr mb.pmb_expr in
       let rec fixup_mexp mexp =
         match mexp.pmod_desc with
         | Pmod_ident { txt = Ldot (m, f); loc }
              when m = staged_defs.modname ->
            { mexp with pmod_desc = Pmod_ident
                (Located.mk (Longident.Lident f) ~loc) }
         | Pmod_constraint (mexp, mty) ->
            { mexp with pmod_desc = Pmod_constraint (fixup_mexp mexp, mty) }
         | _ -> mexp in
       let mexp = rename_module functor_arg_names (fixup_mexp mexp) in
       add_structure_item staged_defs
         (pstr_module
            ~loc
            { mb with
              pmb_name = Located.mk ~loc:Location.none (Some staged_modname);
              pmb_expr = mexp });
       let staged_contents_modname = Option.get mb.pmb_name.txt ^ "_StagedCodeContents_" in
       add_structure_item staged_defs
         (pstr_module ~loc
           (module_binding ~loc ~name:(Located.mk ~loc:Location.none (Some staged_contents_modname))
             ~expr:(pmod_ident ~loc (Located.mk ~loc
               (Longident.Ldot (Longident.Lident staged_modname,
                 "Staged_module"))))));
       add_structure_item staged_defs [%stri
         let modcontext''_ = Ppx_stage.Internal.extend_modcontext
           modcontext''_
           [%e estring ~loc:Location.none (Option.get mb.pmb_name.txt)]
           [%e pexp_ident ~loc:Location.none (Located.mk ~loc:Location.none Longident.(Ldot (Lident staged_modname, "staged_source")))]];
       let module_code_names = StrMap.add (Option.get mb.pmb_name.txt) staged_contents_modname module_code_names in
       {stri with pstr_desc = Pstr_module {mb with pmb_expr =
           pmod_ident ~loc:Location.none (Located.mk ~loc:Location.none (Longident.Ldot (staged_defs.modname, staged_contents_modname)))}}
       :: quasiquote_structure staged_defs functor_arg_names module_code_names rest
    | Pstr_modtype _ ->
       add_structure_item staged_defs stri;
       stri :: quasiquote_structure staged_defs functor_arg_names module_code_names rest
    | Pstr_module mb ->
       let rec collect_functors acc modexpr =
         match modexpr.pmod_desc with
         | Pmod_structure s -> acc, Some s
         | Pmod_functor (Named (ident, mty), body) ->
            let mty = mapper#module_type mty in
            collect_functors ((ident, mty) :: acc) body
         | _ -> acc, None in
       let (functors, body) = collect_functors [] mb.pmb_expr in
       begin match body with
       | None ->
          (* FIXME: does mod renaming happen correctly here? *)
          mapper#structure_item stri
          :: quasiquote_structure staged_defs functor_arg_names module_code_names rest
       | Some body ->
          let staged_modname = Option.get mb.pmb_name.txt ^ "_Staged_" in
          let staged_mod_path = Longident.Ldot (staged_defs.modname, staged_modname) in
          let trans_arg ident =
            { ident with txt = Option.get ident.txt ^ "_StagedArg_" } in
          let sub_functor_arg_names =
            List.fold_left (fun names (ident, _signature) ->
                StrMap.add (Option.get ident.txt) (trans_arg ident).txt names)
               functor_arg_names
               functors in
          let submod = {
            modname =
              if functors = [] then
                staged_mod_path
              else
                Lident staged_modname;
            def_list = []; num_defs = 0
          } in
          let translated = quasiquote_structure submod sub_functor_arg_names module_code_names body in
          let translated =
            if functors = [] then translated else
              let rec apply_functor_args = function
                | [] -> pmod_ident ~loc:Location.none (Located.mk ~loc:Location.none staged_mod_path)
                | (ident, _signature) :: rest ->
                   pmod_apply
                     ~loc:Location.none
                     (apply_functor_args rest)
                     (pmod_ident ~loc:Location.none (Located.mk ~loc:Location.none (Longident.Lident (Option.get ident.txt)))) in
              pstr_module
                ~loc:Location.none
                (module_binding
                  ~loc:Location.none
                  ~name:(Located.mk ~loc:Location.none (Some staged_modname))
                  ~expr:(apply_functor_args functors)) :: translated in
          let rec replace_functors body = function
            | ((ident : string option loc), signature) :: rest ->
               (* FIXME rename and process signature *)
              replace_functors (pmod_functor ~loc:Location.none (Named (ident, signature)) body) rest
            | [] -> body in
          let staged_mod =
            replace_functors
              (pmod_structure ~loc:Location.none (collect_definitions submod))
              (List.map (fun (ident, signature) ->
                  let ident = trans_arg ident in
                  ({ ident with txt = Some ident.txt }, signature))
                functors) in
          let staged_modname = Located.mk ~loc:Location.none (Some staged_modname) in
          add_structure_item staged_defs (pstr_module ~loc:Location.none (module_binding ~loc:Location.none ~name:staged_modname ~expr:staged_mod));
          {stri with pstr_desc = Pstr_module {mb with pmb_expr =
              replace_functors (pmod_structure ~loc:Location.none translated) functors}}
          :: quasiquote_structure staged_defs functor_arg_names module_code_names rest
       end
    | _ ->
       mapper#structure_item stri
       :: quasiquote_structure staged_defs functor_arg_names module_code_names rest

let apply_staging str =
  (* Slightly revolting, but we need to avoid Staged being shadowed by things imported from other modules *)
  let modname = "Staged_" ^ string_of_int (Hashtbl.hash str) in
  let staged_defs = {
      modname = Lident modname;
      def_list = []; num_defs = 0 } in
  add_structure_item
    staged_defs
    (let loc = Location.none in
     [%stri let modcontext''_ = Ppx_stage.Internal.empty_modcontext]);
  let mapped_str = quasiquote_structure staged_defs StrMap.empty StrMap.empty str in
  let inserted = collect_definitions staged_defs in
  let loc = Location.none in
  let modname = Located.mk ~loc (Some modname) in
  match inserted, mapped_str with
  | [], mapped_str -> mapped_str
  | inserted, [{pstr_desc = Pstr_eval (e, ats); pstr_loc}] ->
     let e' = pexp_letmodule ~loc modname (pmod_structure ~loc inserted) e in
     [{ pstr_desc = Pstr_eval (e', ats); pstr_loc }]
  | inserted, [{pstr_desc = Pstr_value(Nonrecursive, [ vb ]); pstr_loc}] ->
     let e' = pexp_letmodule ~loc modname (pmod_structure ~loc inserted) vb.pvb_expr in
     [{ pstr_desc = Pstr_value(Nonrecursive, [ {vb with pvb_expr = e'} ]); pstr_loc}]
  | inserted, mapped_str ->
     pstr_module ~loc (module_binding ~loc ~name:modname ~expr:(pmod_structure ~loc inserted)) :: mapped_str

let () = Ppxlib.Driver.register_transformation "ppx_stage" ~impl:apply_staging
