type 'a t = Ppx_staged_internal of (unit -> 'a) * (unit -> string)

val source : 'a t -> string
val run : 'a t -> 'a
val make : (unit -> 'a) -> (unit -> string) -> 'a t

