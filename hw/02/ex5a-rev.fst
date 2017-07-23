module RevIsOk

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

(* Here is a more efficient (tail-recursive) variant of the list
   reverse function. *)
val reverse : list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]

val rev : l1:list 'a -> l2:list 'a -> Tot (list 'a) (decreases l2)
let rec rev l1 l2 =
  match l2 with
  | []     -> l1
  | hd::tl -> rev (hd::l1) tl

val append_assoc : xs:list 'a -> ys:list 'a -> zs:list 'a -> Lemma
      (ensures (append (append xs ys) zs = append xs (append ys zs)))
let rec append_assoc xs ys zs =
  match xs with
  | [] -> ()
  | x::xs' -> append_assoc xs' ys zs


(* TODO: Prove the following lemma showing the correctness of this
   efficient implementation with respect to the previous simple
   implementation.  You can use the append_assoc lemma above for this,
   but you will probably need to come up with more lemmas. *)
val rev_is_ok : l:list 'a -> Lemma (rev [] l = reverse l)
