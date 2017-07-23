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


val insert : f:('a -> 'a -> Tot bool){total_order 'a f} -> i:'a -> l:list 'a ->
             Tot (r : list 'a { permutation 'a r (i::l)})
let rec insert f i l =
  match l with
  | [] -> [i]
  | hd::tl ->
     if f i hd then i::l
     else hd::(insert f i tl)

(* for some reason, sortedness was not intrinsically provable (#171) *)
val insert_sorted : f:('a -> 'a -> Tot bool){total_order 'a f} -> i:'a -> l:list 'a {sorted f l} ->
                           Lemma (requires True) (ensures (sorted f (insert f i l)))
                           [SMTPat (insert f i l)]
let rec insert_sorted f i l =
  match l with
  | [] -> ()
  | hd :: tl ->
     if f i hd then () else insert_sorted f i tl
                           
val insertion_sort_cmp : f:('a -> 'a -> Tot bool){total_order 'a f} ->
      l:list 'a -> Tot (m:list 'a{sorted f m /\ permutation 'a l m})
let rec insertion_sort_cmp f l =
  match l with
  | [] -> []
  | x::xs -> insert f x (insertion_sort_cmp f xs)
