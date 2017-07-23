module InsertionSort

open IntSort
open FStar.List

(* Explicitly calling sorted_smaller lemma
   (otherwise verification takes a lot longer) *)
val insert : i:int -> l:list int{sorted l} ->
      Tot (m:list int{sorted m /\ permutation (i::l) m})
let rec insert i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else let i_tl = insert i tl in 
          let (z::_) = i_tl in
          if mem z tl then sorted_smaller hd z tl;
          hd::i_tl

(* Solver implicitly uses the lemma: sorted_smaller hd (Cons.hd i_tl) tl *)
val insert_implicit : i:int -> l:list int{sorted l} ->
      Tot (m:list int{sorted m /\ permutation (i::l) m})
let rec insert_implicit i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else hd::(insert_implicit i tl)

val insertion_sort : l:list int -> Tot (m:list int{sorted m /\ permutation l m})
let rec insertion_sort l = match l with
    | [] -> []
    | x::xs -> insert x (insertion_sort xs)
