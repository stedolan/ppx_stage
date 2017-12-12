module Foo (X: Map.OrderedType[@code]) (Y : sig val y : int end) = struct
  module%code X = X
  module%code M = struct[@code]
    let cmp = X.compare
  end
  let c = M.cmp
  let x = [%code M.cmp]
end

module Bar = struct
  module%code A = struct[@code]
    let foo = 42
  end
  let blah = [%code A.foo]
end


module Blah : sig[@code]
  val x : int
end = struct[@code]
  let x = 42
end


module%code A = struct[@code]
  let foo = 42
end
let blah = [%code A.foo]


module%code T = struct[@code]
  type t = float
end

let x : T.t = 42.0


module%code M : sig[@code]
  val x : int
end = struct[@code]
  let x = 10
end


module type Blah = sig
  val x : int
end

module Func (X: Map.OrderedType[@code]) (B : Blah) = struct
  module%code X = X
  module%code M = Map.Make(X)[@code]
  let foo e = [%code M.singleton [%e e] [%e e]]
end

module App = Func (struct[@code] type t = int let compare = compare end) (struct let x = 42 end)

module%code X = struct[@code]
  let bar = 42
end


module JAIO  =struct
module%code M : sig[@code]
  val x : int
end = struct[@code]
  let x = 42
end
let foo y = [%code M.x + [%e y]] (* works *)

let () = Format.printf "%a@." Ppx_stage.print (foo [%code 10])
end

let () = Format.printf "%a@." Ppx_stage.print (App.foo [%code X.bar])


(*
scoping error:

module Bloop (A: Map.OrderedType) = struct
  let foo = [%code A.compare]
end
*)
