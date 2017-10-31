open Migrate_parsetree

open Ast_405
module Ast_lifter = Ast_lifter_405

open Asttypes
open Parsetree
open Ast_mapper
open Ast_helper
open Astring

let expr_extension name pexp =
  match pexp.pexp_desc with
  | Pexp_extension ({ txt; loc }, code) when txt = name ->
     begin match code with
     | PStr [ {pstr_desc=Pstr_eval (e, _); _} ] ->
        Some (e, loc)
     | _ ->
        raise (Location.(Error (error ~loc ("[%" ^ name ^ "] expects an expression"))))
     end
  | _ -> None

let mk_ident ?(loc=Location.none) name =
  let rec go = function
    | [] -> failwith "error: mk_ident []"
    | [x] -> Longident.Lident x
    | field :: rest -> Longident.Ldot(go rest, field) in
  { txt = go (List.rev name); loc }


let find_holes exp =
  let table = Hashtbl.create 20 in
  let count = ref 0 in
  let expr mapper pexp =
    match expr_extension "e" pexp with
    | Some (e, loc) ->
       incr count;
       Hashtbl.add table !count e;
       Exp.ident (mk_ident ["," ^ string_of_int !count])
    | _ -> default_mapper.expr mapper pexp in
  let mapper = { default_mapper with expr } in
  let exp' = mapper.expr mapper exp in
  exp', table


module IM = Ppx_stage_rt.IdentMap

module IntMap = Map.Make (struct type t = int let compare = compare end)

type staged_defs = {
  mutable def_list : (string * expression) list;
  mutable num_defs : int
}

let add_definition defs exp =
  let id = defs.num_defs in
  defs.num_defs <- id + 1;
  let ident = "staged" ^ string_of_int id in
  defs.def_list <- (ident, exp) :: defs.def_list;
  Exp.ident (mk_ident ["Staged"; ident])

let collect_definitions defs =
  let vbs =
    defs.def_list |> List.rev |> List.map (fun (name, body) -> 
      Vb.mk (Pat.var (Location.mknoloc name)) body) in
  Str.value Nonrecursive vbs

let quasiquote staged_defs mapper pexp =
  match expr_extension "stage" pexp with
  | Some (e, loc) ->
     let hole_name h = "hole''_" ^ string_of_int h in

     let exp_with_holes, hole_table = find_holes e in
     let hole_list = Hashtbl.fold (fun k v ks -> k :: ks) hole_table [] |> List.sort compare in
     let hole_bindings = Ppx_stage_rt.analyse_binders exp_with_holes in

     let binding_site_names =
       Hashtbl.fold (fun _hole scope acc ->
         IM.fold (fun name site acc ->
           if IntMap.mem site acc then
             (assert (IntMap.find site acc = name); acc)
           else
             IntMap.add site name acc
         ) scope acc
       ) hole_bindings IntMap.empty in

     let variable_name b =
       let name = IntMap.find b binding_site_names in
       name ^ "''b" ^ string_of_int b in

     let allocate_variables body =
       IntMap.fold (fun site name body ->
         [%expr let [%p Pat.var (Location.mknoloc (variable_name site))] = Ppx_stage_rt.fresh_variable [%e Exp.constant (Pconst_string (name, None))] in [%e body]]
         ) binding_site_names body in

     let hole_bindings_list h =
       let scope = Hashtbl.find hole_bindings h in
       IM.fold (fun name site acc -> site :: acc) scope [] in

     let contents_name h =
       "contents''_" ^ string_of_int h in

     let instantiate_holes body =
       List.fold_right (fun hole body ->
         let hole_args =
           hole_bindings_list hole |> List.map (fun b -> Nolabel, Exp.ident (mk_ident [variable_name b])) in
         let hole_fn = Exp.ident (mk_ident [hole_name hole]) in
         let app = match hole_args with [] -> hole_fn | hole_args -> Exp.apply hole_fn hole_args in
         [%expr let [%p Pat.var (Location.mknoloc (contents_name hole))] = [%e app] in [%e body]]
       ) hole_list body in

     let exp_compute =
       Ppx_stage_rt.substitute_holes exp_with_holes (fun h ->
         let env =
           List.fold_left (fun env site ->
             [%expr Ppx_stage_rt.Environ.add [%e env] [%e Exp.ident (mk_ident [variable_name site])] [%e Exp.ident (mk_ident [IntMap.find site binding_site_names])]])
             [%expr env'']
             (hole_bindings_list h) in
         [%expr Ppx_stage_rt.compute [%e Exp.ident (mk_ident [contents_name h])] [%e env]]) in


     let exp_source =
       let marshalled = Exp.constant (Pconst_string (Marshal.to_string exp_with_holes [], None)) in
       let pat_int n = Pat.constant (Pconst_integer (string_of_int n, None)) in
       let cases = List.map (fun h ->
         let hole_app = List.fold_right (fun site exp ->
           [%expr Ppx_stage_rt.with_renaming
               [%e Exp.ident (mk_ident [variable_name site])]
               [%e Exp.constant (Pconst_string (IntMap.find site binding_site_names, None))]
               [%e exp]])
           (hole_bindings_list h)
           [%expr Ppx_stage_rt.source [%e Exp.ident (mk_ident [contents_name h])]] in
         Exp.case
           (pat_int h)
           [%expr [%e hole_app] ren''])
         hole_list
         @ [Exp.case (Pat.any ()) [%expr assert false]] in
       [%expr
         Ppx_stage_rt.substitute_holes
           (Marshal.from_string [%e marshalled] 0)
           [%e Exp.function_ cases]] in

     let staged_code =
       List.fold_right
         (fun hole code ->
           [%expr fun [%p Pat.var (Location.mknoloc (hole_name hole))] -> 
             [%e code]])
         hole_list
         (allocate_variables
            (instantiate_holes
               [%expr Ppx_stage_rt.Ppx_stage_internal 
                   ((fun env'' -> [%e exp_compute]),
                    (fun ren'' -> [%e exp_source]))])) in

     let staged_code = add_definition staged_defs staged_code in

     let hole_applications =
       hole_list |> List.map (fun hole ->
         let hole_with_bindings =
           List.fold_right
             (fun site body ->
               (* FIXME: rename var to prevent shadowing *)
               [%expr fun [%p Pat.var (Location.mknoloc (IntMap.find site binding_site_names))] ->
                 [%e body]])
             (hole_bindings_list hole)
             (Hashtbl.find hole_table hole) in
         (Nolabel, hole_with_bindings)) in

     (match hole_applications with
     | [] -> staged_code
     | apps -> Exp.apply staged_code apps)
  | _ -> default_mapper.expr mapper pexp

let apply_staging str =
  let staged_defs = { def_list = []; num_defs = 0 } in
  let mapper = { default_mapper with expr = quasiquote staged_defs } in
  let mapped_str = mapper.structure mapper str in
  [%stri module Staged = struct [%%s [collect_definitions staged_defs]] end] :: mapped_str

let () =
  Driver.register ~name:"ppx_stage" Versions.ocaml_405
    (fun _config _cookies -> make_top_mapper
      ~signature:(fun s -> s)
      ~structure:apply_staging)
