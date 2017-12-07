module Foo (X: Map.OrderedType) (Y : sig val y : int end) = struct
  module%code M = struct
    let cmp = X.compare
  end
  let c = M.cmp
  let x = [%code M.cmp]
end

module Bar = struct
  module%code A = struct
    let foo = 42
  end
  let blah = [%code A.foo]
end
