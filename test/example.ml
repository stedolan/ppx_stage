let () = Format.printf "STARTUP@."
let unit = [%stage ()]
let two = [%stage [%e Format.printf "EARLY@."; unit]; 2]
let hello = [%stage "hello"]
let asdf = [%stage string_of_int ([%e two] + [%e two]) ^ [%e hello] ]

let print x =
  Format.printf "[@[%a@]] = [%s]@." Ppx_stage.print x (Ppx_stage.run x)

let () = print asdf

let fn () = [%stage fun x -> [%e Format.printf "STAGING@."; [%stage x]]]

let id2 = [%stage [%e fn ()] [%e hello]]

let () = print id2


let beta code = [%stage [%e code]]

open Ppx_stage
let go a b c =
  [%stage let f x = x in f [%e a]]


(*
(* MetaOCaml nasty example *)
let c () =
  let r = ref [%stage fun z -> z] in 
  let f = [%stage fun x -> [%e r := [%stage fun y -> x]; [%stage 0]]] in 
  [%stage fun x -> [%e f] ([%e !r] 1) ]

let foo = Ppx_stage.run (c ()) 42

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print (c ())

*)

(*
let bad () =
  let c1 =
    let r = ref [%stage fun z->z] in 
    let _ = [%stage fun x -> [%e r := [%stage fun y -> x ]; [%stage 0]]] in 
    !r in
  [%stage fun y -> fun x -> [%e c1]]

let () =
  Format.printf "@[%a@]@." Ppx_stage.print (bad ())
*)


[%%stage
let rset r v =
  let vs' = v :: !r in
  r := vs';
  vs'
]

let foo = [%stage rset]


let foo = [%stage let x = [] in (2 :: x, "3" :: x)]  
let foo = [%stage let f = fun x -> x in (f 2, f "3")]
(*let foo = [%stage let x = ref [] in (rset x 2, rset x "3")]*)

let foo = [%stage let f = fun () -> ref [] in
                  (rset (f ()) 2, rset (f ()) "3")]



[%%stage
let square x = x * x
]

let rec spower n x =
  if n = 0 then [%stage 1]
  else if n mod 2 = 0 then [%stage square [%e spower (n/2) x]]
  else [%stage [%e x] * [%e spower (n-1) x]]


let spower7 = [%stage fun x -> [%e spower 7 [%stage x]]]


let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print spower7

(* let stagestage = [%stage [%stage 2]] *)

let map f =
  [%stage
      let rec go = function
        | [] -> []
        | x :: xs -> [%e f [%stage x]] :: go xs in
      go]

let nest = [%stage fun x -> [%e [%stage [%e [%stage x]]]]]
let three = [%stage [%e nest] 3]

let mapsuc = map (fun x -> [%stage [%e x] + 1])

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print mapsuc


let rec repeat x = function
  | 0 -> [%stage []]
  | n -> [%stage [%e x] :: [%e repeat x (n-1)]]

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print (repeat [%stage 42] 4)




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
  Printf.printf "%s\n" (Ppx_stage.source spower7)
*)
