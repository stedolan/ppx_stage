let () = Format.printf "STARTUP@."
let unit = [%code ()]
let two = [%code [%e Format.printf "EARLY@."; unit]; 2]
let hello = [%code "hello"]
let asdf = [%code string_of_int ([%e two] + [%e two]) ^ [%e hello] ]

let print x =
  Format.printf "[@[%a@]] = [%s]@." Ppx_stage.print x (Ppx_stage.run x)

let () = print asdf

let fn () = [%code fun x -> [%e Format.printf "STAGING@."; [%code x]]]

let id2 = [%code [%e fn ()] [%e hello]]

let () = print id2


let beta code = [%code [%e code]]

open Ppx_stage
let go a b c =
  [%code let f x = x in f [%e a]]


(*
(* MetaOCaml nasty example *)
let c () =
  let r = ref [%code fun z -> z] in 
  let f = [%code fun x -> [%e r := [%code fun y -> x]; [%code 0]]] in 
  [%code fun x -> [%e f] ([%e !r] 1) ]

let foo = Ppx_stage.run (c ()) 42

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print (c ())

*)

(*
let bad () =
  let c1 =
    let r = ref [%code fun z->z] in 
    let _ = [%code fun x -> [%e r := [%code fun y -> x ]; [%code 0]]] in 
    !r in
  [%code fun y -> fun x -> [%e c1]]

let () =
  Format.printf "@[%a@]@." Ppx_stage.print (bad ())
*)


[%%code
let rset r v =
  let vs' = v :: !r in
  r := vs';
  vs'
]

let foo = [%code rset]


let foo = [%code let x = [] in (2 :: x, "3" :: x)]  
let foo = [%code let f = fun x -> x in (f 2, f "3")]
(*let foo = [%code let x = ref [] in (rset x 2, rset x "3")]*)

let foo = [%code let f = fun () -> ref [] in
                  (rset (f ()) 2, rset (f ()) "3")]



[%%code
let square x = x * x
]

let rec spower n x =
  if n = 0 then [%code 1]
  else if n mod 2 = 0 then [%code square [%e spower (n/2) x]]
  else [%code [%e x] * [%e spower (n-1) x]]


let spower7 = [%code fun x -> [%e spower 7 [%code x]]]


let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print spower7

(* let stagestage = [%code [%code 2]] *)

let map f =
  [%code
      let rec go = function
        | [] -> []
        | x :: xs -> [%e f [%code x]] :: go xs in
      go]

let nest = [%code fun x -> [%e [%code [%e [%code x]]]]]
let three = [%code [%e nest] 3]

let mapsuc = map (fun x -> [%code [%e x] + 1])

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print mapsuc


let rec repeat x = function
  | 0 -> [%code []]
  | n -> [%code [%e x] :: [%e repeat x (n-1)]]

let () =
  Format.printf "[@[%a@]]@." Ppx_stage.print (repeat [%code 42] 4)




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
let rec spower n = fun%code x ->
  [%e if n = 0 then [%code 1] else assert false]

let () =
  Printf.printf "%s\n" (Ppx_stage.source spower7)
*)
