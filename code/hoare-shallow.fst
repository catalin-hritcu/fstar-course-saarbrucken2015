module While

open FStar.Heap
open FStar.ST

kind Asrt = heap -> Type

effect Com (a:Type) (p:Asrt) (q:Asrt) = ST a (fun h' -> p h')
                                             (fun _ _ h -> q h)

type Com' (p:Asrt) (q:Asrt) = unit -> Com unit p q

val skip : p:Asrt -> Com unit p p 
let skip (p:Asrt) = ()

type exp (a:Type) (p:Asrt) (q:(a -> Asrt)) =
       unit -> ST a (fun h0 -> p h0) (fun h0 x h1 -> h0=h1 /\ q x h1) 

(* Using equality constraints for better type inference *)
val _while: #p:Asrt -> #q:(bool -> Asrt)
        -> =guard:exp bool p q
        -> =body:(unit -> Com unit (fun h -> p h /\ q true h) p)
        -> Com unit p (fun h -> p h /\ q false h)
let rec _while guard body =
  if guard () then (body (); _while guard body)

val cond: p:Asrt -> q:(bool -> Asrt) -> r:Asrt -> s:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> Com unit (fun h -> q true h) r)
      -> =_else:(unit -> Com unit (fun h -> q false h) s)
      -> Com unit p (fun h -> r h \/ s h)
(* Loss in precision here, since Com does not include 2-state post-conditions *)
let cond guard _then _else = 
  if guard()
  then _then()
  else _else()

val cond2: p:Asrt -> q:(bool -> Asrt) -> r:Asrt -> s:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> Com unit (fun h -> q true h) r)
      -> =_else:(unit -> Com unit (fun h -> q false h) s)
      -> ST unit p (fun h0 _ h1 -> 
                      (q true h0 /\ r h1)
                   \/ (q false h0 /\ s h1))
(* recover precision by dropping back into St *)
let cond2 guard _then _else = 
  if guard()
  then _then()
  else _else()

(* CH: In Hoare logic this is actually even less precise (r = s);
       one has to use explicit weakening *)
val cond3: p:Asrt -> q:(bool -> Asrt) -> r:Asrt
      -> =guard:exp bool p q
      -> =_then:(unit -> Com unit (fun h -> q true h) r)
      -> =_else:(unit -> Com unit (fun h -> q false h) r)
      -> Com unit p (fun h -> r h)
let cond3 guard _then _else = 
  if guard()
  then _then()
  else _else()


(* A sample program written against this API *)
logic type pre (r1:ref int) (r2:ref int) (h:heap) = 
          (contains h r1 
           /\ contains h r2
           /\ sel h r1 <= sel h r2)

logic type post  (r1:ref int) (r2:ref int) (b:bool) (h:heap) = 
          (b = (sel h r1 <> sel h r2))

(* equalize r1 r2: 
   requires the contents of r1 to be less than or equal to r2
            Repeatedly increments r1
   ensures the contents of r1 is equal to to r2
 *)
val equalize: r1:ref int -> r2:ref int
              -> Com unit (requires (pre r1 r2))
                          (ensures (fun h -> sel h r1 = sel h r2))
let equalize r1 r2 =
  let test : exp bool (pre r1 r2) (post r1 r2) =
    (* At the moment, you need to decorate these functions with their
       types; type inference is not yet smart enough to do it for you
       ... it's relatively easy to do ... on my list *)
    fun () -> read r1 <> read r2 in

  let body : unit -> Com unit (fun h -> pre r1 r2 h /\ post r1 r2 true h)
                              (pre r1 r2) = 
    fun () -> write r1 (read r1 + 1) in

  _while test body

(* Exercise:

     Relax the pre-condition that r1 is less than or equal to r2 
     so that it works with any pair of refs.
*)
