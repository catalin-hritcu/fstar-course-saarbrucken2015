module FoldLeft

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

// BEGIN: FoldLeftInteresting
val fold_left: f:('b -> 'a -> Tot 'a) -> l:list 'b -> 'a -> Tot 'a
let rec fold_left f l a = match l with
  | Nil -> a
  | Cons hd tl -> fold_left f tl (f hd a)

val append_cons: l:list 'a -> hd:'a -> tl:list 'a ->
                 Lemma (append l (Cons hd tl) = append (append l (Cons hd Nil)) (tl))
let rec append_cons l hd tl = match l with
  | Nil -> ()
  | Cons hd' tl' ->
    append_cons tl' hd tl

val snoc_append: l:list 'a -> h:'a -> Lemma (snoc l h = append l (Cons h Nil))
let rec snoc_append l h = match l with
  | Nil -> ()
  | Cons hd tl ->
    snoc_append tl h

val reverse_append: tl:list 'a -> hd:'a ->
                  Lemma (reverse (Cons hd tl) = append (reverse tl) (Cons hd Nil))
let reverse_append tl hd = snoc_append (reverse tl) hd

val fold_left_cons_is_reverse: l:list 'a -> l':list 'a ->
                             Lemma (fold_left Cons l l' = append (reverse l) l')
let rec fold_left_cons_is_reverse l l' = match l with
  | Nil -> ()
  | Cons hd tl ->
    fold_left_cons_is_reverse tl (Cons hd l');
    append_cons (reverse tl) hd l';
    reverse_append tl hd
// END: FoldLeftInteresting

(* Here is a more explicit proof of the same statement *)

val append_propr : h : 'a -> l1 : list 'a -> l2 : list 'a ->
      Lemma (append (snoc l1 h) l2 = append l1 (Cons h l2))
let rec append_propr h l1 l2 =
  match l1 with
  | [] -> ()
  | hd :: tl -> append_propr h tl l2 

val fold_left_cons_is_reverse': l:list 'a -> l':list 'a ->
      Lemma (fold_left Cons l l' = append (reverse l) l')
let rec fold_left_cons_is_reverse' l l' =
  match l with
  | [] -> ()
  | hd :: tl -> assert(fold_left Cons l l' = fold_left Cons tl (hd :: l'));
                fold_left_cons_is_reverse' tl (hd::l');
                assert(fold_left Cons l l' = append (reverse tl) (hd :: l'));

                assert(append (reverse l) l' = append (snoc (reverse tl) hd) l');
                append_propr hd (reverse tl) l';
                assert(append (reverse l) l' = append (reverse tl) (hd :: l'))

(* In fact fold_left_cons_is_reverse is just a generalization needed
   for proving fold_left_cons_is_reverse' below *)

val app_nil : l:list 'a -> Lemma (append l [] = l)
let rec app_nil l = match l with [] -> () | _::l' -> app_nil l'

val fold_left_cons_is_reverse_final: l:list 'a ->
                             Lemma (fold_left Cons l [] = reverse l)
let fold_left_cons_is_reverse_final l =
  fold_left_cons_is_reverse l []; app_nil (reverse l)
