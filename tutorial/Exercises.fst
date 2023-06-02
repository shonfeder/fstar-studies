module Exercises

/// Part 1
open FStar.Mul

val incr : x:int -> y:int{y = x + 1}
let incr x = x + 1

val max : x:int -> y:int -> z:int{if x > y then z = x else z = y}
let max x y = if x > y then x else y

// val factorial : n:int -> m:int{m > n}
// val factorial : n:nat -> m:nat{if n = 0 then m = 1 else m >= n * (n - 1)}
let rec factorial (n:nat)
  : nat
  = if n = 0
    then 1
    else n * factorial (n - 1)


///  Part 2
val apply (a b:Type) (f:a -> b) : a -> b
val compose (a b c:Type) (f: b -> c) (g : a -> b) : a -> c

let apply a b f = fun x -> f x
let compose a b d f g = fun x -> f (g x)

val twice (a:Type) (f: a -> a) (x:a) : a
let twice a f x = f (f x)

/// Part 3

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

val append (#a:Type) (l1 l2: list a)
  : l:list a { length l = length l1 + length l2 }
let rec append l1 l2
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

/// Proofs of termination

let append_lists_yields_lists_with_sum_of_lengths =
  assert (forall  (a:Type) (l1:list a) (l2:list a). length (append l1 l2) = length l1 + length l2 )

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

let rec fib (a b n:nat) : Tot nat (decreases n) =
   match n with
   | 0 -> a
   | _ -> fib b (a+b) (n-1)

let fibonacci1 n = fib 1 1 n

val rev_aux : #a:Type -> list a -> l2:list a -> Tot (list a) (decreases l2)
let rec rev_aux l1 l2 =
  match l2 with
  | []     -> l1
  | hd :: tl -> rev_aux (hd :: l1) tl

val rev : #a:Type -> list a -> list a
let rev l = rev_aux [] l


/// Lemmas and proofs by induction

let rec factorial_is_pos : x:int{x >= 0} -> Lemma (factorial x > 0) = function
  | 0 -> assert (factorial 0 = 1)
  | n -> factorial_is_pos (n - 1)

let rec factorial_is_greater_than_arg : x:int{x > 2} -> Lemma (factorial x > x) = function
  | 3 -> ()
  | n -> factorial_is_greater_than_arg (n - 1)

let rec fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n) = function
  | 2 -> ()
  | n -> fibonacci_greater_than_arg (n - 1)

let rec app #a (l1 l2: list a): list a = match l1 with
    | []      -> l2
    | hd :: tl -> hd :: app tl l2

let rec app_length #a (l1 l2: list a) : Lemma (length (app l1 l2) = length l1 + length l2) =
  match l1 with
  | []      -> ()
  | _ :: tl -> app_length tl l2

let rec reverse #a : list a -> list a = function
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]

/// Apalache notes
type space = { heatingOn: bool
             ; temperature: int
             ; beeping: bool
             }

type time : nat -> Type =
  | Init : space -> time 0
  | Tick : #i:nat -> space -> time (i + 1)

let step = space -> option space

let init : space -> time 0 =
  fun s -> Init s

let t0 : space = {heatingOn = false; temperature = 20; beeping = false}

let pressButton
  : s0:space{ ~ s0.heatingOn }
  -> s1:space{ s1.heatingOn }
  = fun s -> {s with heatingOn = true}

let failover
  : s0:space{ s0.heatingOn
            /\ s0.temperature >= 100
            }
  -> s1:space{ ~ s1.heatingOn
            /\   s1.beeping
            /\   s1.temperature = s0.temperature
            }
  = fun s -> { s with heatingOn = false
                 ; beeping   = true
                 }

let heat
  : s0:space{ s0.heatingOn
            /\ s0.temperature < 100
            }
  -> s1:space{   s1.heatingOn
            /\ ~ s1.beeping
            /\   s1.temperature = s0.temperature + 1
            }
  = fun s -> { s with temperature = s.temperature + 1
                 ; beeping     = false
                 }

let depressButton
  : s0:space{ s0.heatingOn }
  -> s1:space{ ~ s1.heatingOn
            /\ ~ s1.beeping
            /\   s1.temperature = s0.temperature
            }
  = fun s -> { s with heatingOn = false
                 ; beeping   = false
                 }

// let init : n
// type st = switch \/ int

// let x = assert (forall (n:nat). factorial n >= 1)

// x:nat * s:(x -> t) : state
// asserts let us state invariants
// bounded checking is enforced by the need for functions to be total, so we
// must always count down from a number of states.
//
// a transition is a partial function f -> s -> option s'{f(s)}
// - where the the type for s' depends in  `f`, if can be applied
