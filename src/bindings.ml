open Result

let return x = Ok x
let ( let* ) x f = bind x f
