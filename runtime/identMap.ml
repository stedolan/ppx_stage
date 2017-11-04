type ident = string
include Map.Make (struct type t = ident let compare = compare end)
