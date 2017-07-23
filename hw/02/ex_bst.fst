module BinarySearchTreeBasic

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val all : p:(int -> Tot bool) -> t:tree ->
            Tot (r:bool{r <==> (forall x. in_tree x t ==> p x)})
let rec all p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && all p t1 && all p t2

val lt : int -> int -> Tot bool
let lt n1 n2 = n1 < n2

val gt : int -> int -> Tot bool
let gt n1 n2 = n1 > n2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> all (gt n) t1 && all (lt n) t2 && is_bst t1 && is_bst t2
(*
  gt n = fun n' -> n > n' -- predicate testing if argument is less than n
  lt n = fun n' -> n < n' -- predicate testing if argument is greater than n
*)


val search : x:int -> t:tree{is_bst t} -> Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert : x:int -> t:tree{is_bst t} ->
             Tot (r:tree{is_bst r /\
                  (forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)

val insert' : int -> tree -> Tot tree
let rec insert' x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert' x t1) t2
                    else               Node n t1 (insert' x t2)

(* TODO: Give an extrinsic proof showing the correctness of insert' 
 * (i.e. show the same properties that were shown for insert). *)



val find_max : tree -> Tot int
(* TODO: Define the function find_max (it finds the largest element in a tree)
 * and refine its type so that the function delete (below, in comments) 
 * tpyechecks *)

(*
val delete : x:int -> t:tree{is_bst t} ->
  Tot (r:tree{is_bst r /\ not (in_tree x r)  /\ 
              (forall y. x <> y ==> (in_tree y t = in_tree y r))}) (decreases t)
let rec delete x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _           -> let y = find_max t1 in 
                                       Node y (delete y t1) t2
                    else if x < n then Node n (delete x t1) t2 
                                  else Node n t1 (delete x t2)
*)




assume val find_max' : tree -> Tot int

val delete' : x : int -> t:tree -> Tot tree (decreases t)
let rec delete' x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then match (t1, t2) with
                      | (Leaf, Leaf) -> Leaf
                      | (_, Leaf) -> t1
                      | (Leaf, _) -> t2
                      | _ -> 
                          let y = find_max' t1 in 
                            Node y (delete' y t1) t2
                    else if x < n then Node n (delete' x t1) t2 
                         else Node n t1 (delete' x t2)

(* TODO: Give an extrinsic proof showing the correctness of delete' 
 * (i.e. show the same properties that were shown for delete) 
 * Hint: in the process you need to write the function find_max' and give an 
 * extrinsic proof of correctness for it.
 * Why can you not reuse the previously defined find_max? *)
