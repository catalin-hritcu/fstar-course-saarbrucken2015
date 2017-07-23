module MergeSort

open FStar.List
open IntSort

(* TODO (optional exercise): verify this code *)

val split: l:list int -> Tot (list int * list int)
let rec split (x::y::l) =
  match l with
    | [] -> [x], [y]
    | [x'] -> x::[x'], [y]
    | _ -> let l1, l2 = split l in
           x::l1, y::l2

val merge: l1:list int -> l2:list int -> Tot (list int)
let rec merge l1 l2 = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if h1 <= h2
                        then h1::(merge tl1 l2)
                        else h2::(merge l1 tl2)

val mergesort: l:list int -> Pure (list int)
      (requires True)
      (ensures (fun r -> sorted r /\ permutation l r
        /\ decreases (length l)))
let rec mergesort l = match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let (l1, l2) = split l in
    let sl1 = mergesort l1 in
    let sl2 = mergesort l2 in
    merge sl1 sl2
