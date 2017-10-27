let two = [%stage 2]
let asdf = [%stage 40 + [%e two]]

let () =
  Printf.printf "[%s] = [%d]\n" (Ppx_stage_rt.source asdf) (Ppx_stage_rt.run asdf)

let square x = x * x

let rec spower n x =
  if n = 0 then [%stage 1]
  else if n mod 2 = 0 then [%stage square [%e spower (n/2) x]]
  else [%stage [%e x] * [%e spower (n-1) x]]

(*let spower7 = [%stage fun x -> [%e spower 7 [%stage x]]]*)

let rec spower n = fun%stage x ->
  [%e if n = 0 then [%stage 1] else assert false]

let () =
  Printf.printf "%s\n" (Ppx_stage_rt.source spower7)
