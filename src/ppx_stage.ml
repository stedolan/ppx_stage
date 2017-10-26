open Migrate_parsetree
open Ast_404

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
        raise (Location.(Error (error ~loc "[%expr] expects an expression")))
     end
  | _ -> None

let mk_ident name =
  let rec go = function
    | [] -> failwith "error: mk_ident []"
    | [x] -> Longident.Lident x
    | field :: rest -> Longident.Ldot(go rest, field) in
  { txt = go (List.rev name); loc = Location.none }


let unquote mapper pexp =
  match expr_extension "e" pexp with
  | Some (e, _) -> Exp.(apply (ident (mk_ident ["Ppx_stage_rt"; "value"])) [Nolabel, e])
  | _ -> default_mapper.expr mapper pexp

let next_id = ref 0
let marker = "__ppx_stage_quasiquote_"
let fresh () =
  incr next_id;
  !next_id

let record_qq table mapper pexp =
  match expr_extension "e" pexp with
  | Some (e, loc) ->
     let id = fresh () in
     Hashtbl.add table id e;
     let name = marker ^ string_of_int id in
     { pexp_loc = loc;
       pexp_attributes = [];
       pexp_desc = Pexp_ident { txt = Longident.Lident name; loc } }
  | _ -> default_mapper.expr mapper pexp

let splice table s =
  let rec go s =
    let open String.Sub in
    match cut ~sep:(of_string marker) s with
    | None -> [`Str s]
    | Some (s, rest) ->
       let (id, rest) =
         span ~sat:(function '0'..'9' -> true | _ -> false) rest in
       `Str s :: `Exp (Hashtbl.find table (int_of_string (to_string id))) :: go rest in
  let parts = go (String.Sub.v s) in
  let str_append = mk_ident ["Pervasives"; "^"] in
  List.fold_right (fun a e ->
    let part = match a with
      | `Str s -> Exp.constant (Pconst_string (String.Sub.to_string s, None))
      | `Exp e -> Exp.(apply (ident (mk_ident ["Ppx_stage_rt"; "source"])) [Nolabel, e]) in
    Exp.(apply (ident str_append) [Nolabel, part; Nolabel, e])) 
    parts
    (Exp.constant (Pconst_string ("", None)))
  

let quasiquote mapper pexp =
  match expr_extension "expr" pexp with
  | Some (e, loc) ->
     let unquoter = { default_mapper with expr = unquote } in
     let raw = unquoter.expr unquoter e in
     let table = Hashtbl.create 20 in
     let recorder = { default_mapper with expr = record_qq table } in
     let source = recorder.expr recorder e in
     let buf = Buffer.create 100 in
     let formatter = Format.formatter_of_buffer buf in
     Pprintast.expression formatter source;
     Format.pp_print_flush formatter ();
     let source = splice table (Buffer.contents buf) in
     Exp.(apply (ident (mk_ident ["Ppx_stage_rt"; "make"])) [Nolabel, raw; Nolabel, source])
  | _ -> default_mapper.expr mapper pexp

let mapper _config _cookies =
  { default_mapper with expr = quasiquote }

let () =
  Driver.register ~name:"ppx_stage" Versions.ocaml_404 mapper
