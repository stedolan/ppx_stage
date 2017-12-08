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
  let foo = [%code X.compare]
end

(*
scoping error:

module Bloop (A: Map.OrderedType) = struct
  let foo = [%code A.compare]
end
*)
