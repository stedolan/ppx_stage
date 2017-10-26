let two = Ppx_stage_rt.make 2 "2"
let asdf = [%expr 40 + [%e two]]

let () =
  let (x, s) = asdf in
  Printf.printf "[%s] = [%d]\n" s x
