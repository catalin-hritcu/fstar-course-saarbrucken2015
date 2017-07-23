module Fibonacci

open FStar.Heap
open FStar.ST

val fib_tot : x : nat -> Tot nat
let rec fib_tot x = if x <= 1 then 1 else fib_tot (x-1) + fib_tot (x-2)


val fib : r1:ref nat -> r2:ref nat -> ST unit
      (requires (fun h -> True))
      (ensures (fun h0 a h1 -> exists x.
                  equal h1 (upd (upd h0 r1 x) r2 (fib_tot (sel h0 r1)))))
let rec fib r1 r2 =
  let tmp = !r1 in
  if tmp <= 1
    then r2 := 1
  else 
    (r1 := tmp - 1;
     fib r1 r2;
     let tmp' = read r2 in 
     r1 := tmp - 2;
     fib r1 r2;
     r2 := !r2 + tmp')


val fib' : r1:ref nat -> r2:ref nat -> ST unit
      (requires (fun h -> True))
      (ensures (fun h0 a h1 -> sel h1 r2 = fib_tot (sel h0 r1)))
let fib' r1 r2 = fib r1 r2

