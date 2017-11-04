module M = Staged
open Strymonas

module K = struct
module Staged = M


let iota n = unfold (fun n -> [%code Some ([%e n],[%e n]+1)]) n

(* Example from the paper *)
let example arr1 =
 zip_with (fun e1 e2 -> [%code ([%e e1],[%e e2])])
 (* First stream to zip *)
 (of_arr arr1
   |> map (fun x -> [%code [%e x] * [%e x]])
   |> take [%code 12]
   |> filter (fun x -> [%code [%e x] mod 2 = 0])
   |> map (fun x -> [%code [%e x] * [%e x]]))
 (* Second stream to zip *)
 (iota [%code 1]
   |> flat_map (fun x -> iota [%code [%e x]+1] |> take [%code 3])
   |> filter (fun x -> [%code [%e x] mod 2 = 0]))
 |> fold (fun z a -> [%code [%e a] :: [%e z]]) [%code []]

let () =
  Format.printf
    "@[%a@]@."
    Ppx_stage.print [%code fun arr1 -> [%e example [%code arr1]]]

let cart = fun (arr1, arr2) ->
  of_arr arr1
  |> flat_map (fun x -> 
       of_arr arr2 |> map (fun y -> [%code [%e x] * [%e y]]))
  |> fold (fun z a -> [%code [%e z] + [%e a]]) [%code 0]

let () =
  let c = [%code fun arr1 arr2 -> [%e cart ([%code arr1],[%code arr2 ])]] in
  Format.printf
    "@[%a@]@."
    Ppx_stage.print c

end
