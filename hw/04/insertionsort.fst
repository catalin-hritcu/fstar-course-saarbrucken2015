module InsertionSort

open IntSort
open FStar.List

val insert : i:int -> l:list int -> Tot (list int)
let rec insert i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else hd::(insert i tl)

(* TODO: strengthen the type of insert, or prove a lemma about it to
         make insertion_sort type-check
val insertion_sort : l:list int -> Tot (m:list int{sorted m /\ permutation l m})
let rec insertion_sort l = match l with
    | [] -> []
    | x::xs -> insert x (insertion_sort xs)
*)
