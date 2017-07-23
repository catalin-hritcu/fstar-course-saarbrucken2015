module Swap

open FStar.Heap
open FStar.ST

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

val swap : #a:Type -> r1:ref a -> r2:ref a -> ST unit
      (requires (fun h' -> True))
      (ensures (fun h' _ h ->
                  let x1 = sel h' r1 in
                  let x2 = sel h' r2 in
                  equal h (upd (upd h' r1 x2) r2 x1)))
let swap (#a:Type) r1 r2 =
  let tmp = !r1 in
  r1 := !r2;
  r2 := tmp

