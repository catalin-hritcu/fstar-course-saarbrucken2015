module SimpleConditionals

open FStar.Heap
open FStar.ST

val simple_cond : x:ref nat -> y:ref nat -> z:ref nat -> ST unit
      (requires (fun h' -> contains h' x /\ contains h' y /\ contains h' z
                        /\ x <> z /\ y <> z))
      (ensures (fun _ _ h -> (sel h z + sel h x = sel h y) \/
                             (sel h z + sel h y = sel h x)))
let simple_cond x y z =
  if read x < read y then
    write z (read y - read x)
  else
    write z (read x - read y)
