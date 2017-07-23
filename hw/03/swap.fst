module Swap

open FStar.Heap
open FStar.ST

(* For St
type pre = heap -> Type0
type post (a:Type) = heap -> a -> heap -> Type0

type heap

val sel :       a:Type -> heap -> ref a -> Tot a
val upd :       a:Type -> heap -> ref a -> a -> Tot heap
val equal:      heap -> heap -> Tot bool

sel (upd h r v) r = v
sel (upd h r v) r' = sel h r'   if r <> r'

val (!): a:Type -> r:ref a -> ST a
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> equal h0 h1 /\ x==sel h0 r))

val (:=): a:Type -> r:ref a -> v:a -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> equal h1 (upd h0 r v)))
*)

val swap_add_sub : r1:ref int -> r2:ref int -> ST unit
      (requires (fun h' -> r1<>r2))
      (ensures (fun h' _ h ->
                  let x1 = sel h' r1 in
                  let x2 = sel h' r2 in
                  equal h (upd (upd h' r1 x2) r2 x1)))
let swap_add_sub r1 r2 =
  r1 := !r1 + !r2;
  r2 := !r1 - !r2;
  r1 := !r1 - !r2

(* TODO: Define a more natural variant of swap that works for
   references containing any type 'a. Give it the same specification
   as swap_add_sub, or a slightly stronger one if you can find one.
   Hint: do not use allocation for the temporary. *)
