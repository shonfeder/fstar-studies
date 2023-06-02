module Part2.Polymorphism

val apply (a b:Type) (f:a -> b) : a -> b
val compose (a b c:Type) (f: b -> c) (g : a -> b) : a -> c

let apply a b f = fun x -> f x
let compose a b d f g = fun x -> f (g x)

val twice (a:Type) (f: a -> a) (x:a) : a
let twice a f x = f (f x)
