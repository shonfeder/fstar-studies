module Main

/// For any type [a], we can construct the type of length-indexed lists of
/// values of that type.
///
/// In the [Cons] constructor, the indexing [nat] is an implicit argument,
/// indicated by the preceding [#]: the type system will try to infer the value
/// for this argument, allowing us to ommit it at the call sight.
type vec (a:Type) : nat -> Type =
  | Nil  : vec a 0
  | Cons : hd:a -> #n:nat -> tl:vec a n -> vec a (n + 1)

/// To retrieve the length of a vector, we just fetch it out of the type.
///
/// Note that we use the following convention below: implicit arguments are on
/// the lhs of the [=] and explicit arguments appear in the function defined on
/// the rhs.
val length : #a:Type -> #n:nat -> vec a n -> n:nat
let length #a #n = fun _ -> n

/// The constraint [n > 0] in the curly braces is a refinement on the indexing
/// [n : nat], that will statically guarantee [hd] can never be called on empty
/// [vec]s. This allows us to ommit matching on the [Nil] constructor.
val hd : #a:Type -> #n:nat{n > 0} -> vec a n -> a
let hd #a #n = fun (Cons x tl) -> x

val tl : #a:Type -> #n:nat{n > 0} -> vec a n -> vec a (n - 1)
let tl #a #n = fun (Cons x tl) -> tl

/// Again, the refinement constraint gives a static guarantee that this indexing
/// function can never be called with an indexing argument that would lead to
/// and out of bounds error.
val nth : #a:Type -> #m:nat -> n:nat{n < m} -> vec a m -> a
let rec nth #a #m =
  fun n xs -> match n with
         | 0 -> hd xs
         | n -> nth (n - 1) (tl xs)

val append : #a:Type -> #n1:nat -> #n2:nat -> vec a n1 -> vec a n2 -> vec a (n1 + n2)
let rec append #t #n1 #n2 =
  fun xs ys -> match xs with
          | Nil -> ys
          | Cons x xs -> Cons x (append xs ys)

val zip : #a:Type -> #b:Type -> #n:nat -> vec a n -> vec b n -> vec (a * b) n
let rec zip #t1 #t2 #n =
  fun as bs -> match n with
          | 0 -> Nil
          | n -> Cons (hd as, hd bs) (zip (tl as) (tl bs))

/// A simple predicate for use in the type refinement in definition for
/// [of_list] which follows.
let list_is_length ls n =
  FStar.List.Tot.length ls = n

/// [of_list] takes us from a [l : list a] (without a length index in its type!)
/// to a [vec a n], under the assumption that [list_of_length l n] holds AT
/// COMPILE TIME.
val of_list : #a:Type -> #n:nat -> l:(list a){list_is_length l n} -> vec a n
let rec of_list #t #n =
  fun ls -> match ls with
       | []   -> Nil
       | x::xs -> Cons x (of_list #t #(n - 1) xs)

val to_list : #a:Type -> #n:nat -> vec a n -> list a
let rec to_list #t #n =
  fun xs -> match xs with
       | Nil -> []
       | Cons x xs -> x :: (to_list xs)

/// These are static, compile time assertions.
let _ = assert (((Cons 1 (Cons 2 Nil))) = of_list [1; 2])
let _ = assert ([1; 2] = to_list (Cons 1 (Cons 2 Nil)))
let _ =
  let vec_a = of_list #int #3 [1; 2; 3] in
  let vec_b = of_list #int #3 [3; 2; 1] in
  let zipped = zip vec_a vec_b in
  assert ([(1, 3); (2, 2); (3, 1)] = to_list zipped)

val rev : #a:Type -> #n:nat -> vec a n -> vec a n
let rec rev #a #n =
  fun xs -> match xs with
       | Nil -> Nil
       | Cons x xs -> Cons x (rev xs)

// TODO Figure out how this working when it's much simpler than the code in the
// tutorial. Ask on the discord?
// See if I can view how Z3 is reaching the conclusion.

val rev_is_involutive : #a:Type -> #n:nat -> v:vec a n -> Lemma (rev (rev v) == v)
let rec rev_is_involutive #a #n = fun xs -> 
    match xs with
    | Nil -> ()
    | Cons x xs -> rev_is_involutive xs
