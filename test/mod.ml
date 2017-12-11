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



module Func (X: Map.OrderedType[@code]) = struct
  module%code X = X
  let foo e = [%code X.compare [%e e] [%e e]]
end

module App = Func (struct[@code] type t = int let compare = compare end)

module%code X = struct[@code]
  let bar = 42
end

let () = Format.printf "%a@." Ppx_stage.print (App.foo [%code X.bar])


(*
scoping error:

module Bloop (A: Map.OrderedType) = struct
  let foo = [%code A.compare]
end
*)
