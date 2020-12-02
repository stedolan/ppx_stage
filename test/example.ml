let () = Format.printf "STARTUP@."
let unit = [%code ()]
let two = [%code [%e Format.printf "EARLY@."; unit]; 2]
let hello = [%code "hello"]
let asdf = [%code string_of_int ([%e two] + [%e two]) ^ [%e hello] ]

let print x =
  Format.printf "@[%a@] (* = %S*)@." Ppx_stage.print x (Ppx_stage.run x)

let printc x =
  Format.printf "@[%a@]@." Ppx_stage.print x


let () = print asdf

let plus1 = fun%staged x -> x + 1

let fn () = [%code fun x -> [%e Format.printf "STAGING@."; x]]

let id2 = [%code [%e fn ()] [%e hello]]

let () = print id2


let beta code = [%code [%e code]]

let go a _b _c =
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


module%code RSet = struct[@code]
  let rset r v =
    let vs' = v :: !r in
    r := vs';
    vs'
end

let () = printc [%code RSet.rset]


let () = printc [%code let x = [] in (2 :: x, "3" :: x)]
let () = printc [%code let f = fun x -> x in (f 2, f "3")]

let () = printc [%code let f = fun () -> ref [] in
                  (RSet.rset (f ()) 2, RSet.rset (f ()) "3")]



module%code Square = struct[@code]
  let square x = x * x
end

let rec spower n x =
  if n = 0 then [%code 1]
  else if n mod 2 = 0 then [%code Square.square [%e spower (n/2) x]]
  else [%code [%e x] * [%e spower (n-1) x]]


let () = printc [%code fun x -> [%e spower 7 [%code x]]]

let map f =
  [%code
      let rec go = function
        | [] -> []
        | x :: xs -> [%e f [%code x]] :: go xs in
      go]

let nest = [%code fun x -> [%e [%code [%e [%code x]]]]]
let three = [%code [%e nest] 3]
let () = printc three

let () = printc (map (fun x -> [%code [%e x] + 1]))

let rec repeat x = function
  | 0 -> [%code []]
  | n -> [%code [%e x] :: [%e repeat x (n-1)]]

let () = printc (repeat [%code 42] 4)


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
