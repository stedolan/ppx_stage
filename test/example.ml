let () = Format.printf "STARTUP@."
let unit = [%stage ()]
let two = [%stage [%e Format.printf "EARLY@."; unit]; 2]
let hello = [%stage "hello"]
let asdf = [%stage string_of_int (40 + [%e two]) ^ [%e hello] ]

let print x =
  Format.printf "[@[%a@]] = [%s]@." Ppx_stage_rt.print x (Ppx_stage_rt.run x)

let () = print asdf

let fn () = [%stage fun x -> [%e Format.printf "STAGING@."; Ppx_stage_rt.of_variable x]]

let id2 = [%stage [%e fn ()] [%e hello]]

let () = print id2


let beta code = [%stage [%e code]]



(* MetaOCaml nasty example *)
(*
let c =
  let r = ref [%stage fun z -> z] in 
  let f = [%stage fun x -> [%e r := [%stage fun y -> x]; [%stage 0]]] in 
  [%stage fun x -> [%e f] ([%e !r] 1) ]
*)

(*
let square x = x * x

let rec spower n x =
  if n = 0 then [%stage 1]
  else if n mod 2 = 0 then [%stage square [%e spower (n/2) x]]
  else [%stage [%e x] * [%e spower (n-1) x]]


let spower7 = [%stage fun x -> [%e spower 7 (Ppx_stage_rt.of_variable x)]]


let () =
  Format.printf "[@[%a@]]@." Ppx_stage_rt.print spower7
*)

(* let stagestage = [%stage [%stage 2]] *)

let map f =
  [%stage
      let rec go = function
        | [] -> []
        | x :: xs -> [%e f (Ppx_stage_rt.of_variable x)(*[%stage x]*)] :: go xs in
      go]

let mapsuc = map (fun x -> [%stage [%e x] + 1])

let () =
  Format.printf "[@[%a@]]@." Ppx_stage_rt.print mapsuc


let rec repeat x = function
  | 0 -> [%stage []]
  | n -> [%stage [%e x] :: [%e repeat x (n-1)]]

let () =
  Format.printf "[@[%a@]]@." Ppx_stage_rt.print (repeat [%stage 42] 4)




(*
-->
let map f =
  let x₁ = fresh "x" in
  let p1 = f x₁ in
  (fun γ →
    let rec go = function
    | [] → []
    | x :: xs → p1 (γ , x₁ := x) :: go xs in
   go)

map : (α code → β code) → (α list → β list) code


*)


(*
let rec spower n = fun%stage x ->
  [%e if n = 0 then [%stage 1] else assert false]

let () =
  Printf.printf "%s\n" (Ppx_stage_rt.source spower7)
*)
