module M = Staged
open Strymonas

module K = struct
module Staged = M


let iota n = unfold (fun n -> [%stage Some ([%e n],[%e n]+1)]) n

(* Example from the paper *)
let example arr1 =
 zip_with (fun e1 e2 -> [%stage ([%e e1],[%e e2])])
 (* First stream to zip *)
 (of_arr arr1
   |> map (fun x -> [%stage [%e x] * [%e x]])
   |> take [%stage 12]
   |> filter (fun x -> [%stage [%e x] mod 2 = 0])
   |> map (fun x -> [%stage [%e x] * [%e x]]))
 (* Second stream to zip *)
 (iota [%stage 1]
   |> flat_map (fun x -> iota [%stage [%e x]+1] |> take [%stage 3])
   |> filter (fun x -> [%stage [%e x] mod 2 = 0]))
 |> fold (fun z a -> [%stage [%e a] :: [%e z]]) [%stage []]

let () =
  Format.printf
    "@[%a@]@."
    Ppx_stage.print [%stage fun arr1 -> [%e example [%stage arr1]]]

let cart = fun (arr1, arr2) ->
  of_arr arr1
  |> flat_map (fun x -> 
       of_arr arr2 |> map (fun y -> [%stage [%e x] * [%e y]]))
  |> fold (fun z a -> [%stage [%e z] + [%e a]]) [%stage 0]

let () =
  let c = [%stage fun arr1 arr2 -> [%e cart ([%stage arr1],[%stage arr2 ])]] in
  Format.printf
    "@[%a@]@."
    Ppx_stage.print c

end
