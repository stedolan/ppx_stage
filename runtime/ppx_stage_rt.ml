type 'a t = Ppx_staged_internal of (unit -> 'a) * (unit -> string)

let source (Ppx_staged_internal (a, s)) = s ()
let run (Ppx_staged_internal (a, s)) = a ()

let make a s = Ppx_staged_internal (a, s)

