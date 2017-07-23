module InsertionSortCmp

open FStar.List

val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> f x y && sorted f (y::xs)

opaque type permutation (a:Type) (l1:list a) (l2:list a) =
    length l1 = length l2 /\ (forall n. mem n l1 == mem n l2)

type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 == a2)       (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality      *)


val insert : f:('a -> 'a -> Tot bool) -> i:'a -> l:list 'a -> Tot (list 'a)
let rec insert f i l =
  match l with
  | [] -> [i]
  | hd::tl ->
     if f i hd then i::l
     else hd::(insert f i tl)

(* TODO: make this type-check
val insertion_sort_cmp : f:('a -> 'a -> Tot bool){total_order 'a f} ->
      l:list 'a -> Tot (m:list 'a{sorted f m /\ permutation 'a l m})
let rec insertion_sort_cmp f l =
  match l with
  | [] -> []
  | x::xs -> insert f x (insertion_sort_cmp f xs)
*)
