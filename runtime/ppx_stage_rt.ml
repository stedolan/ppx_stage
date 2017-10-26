type 'a t = 'a * string

let source (a, s) = s
let value (a, s) = a

let make a s = a, s
