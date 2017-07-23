module Hoare
open Expressions
open SimplerWhile

kind Asrt = heap -> Type

type asrt_impl (p:Asrt) (q:Asrt) = (forall h. p h ==> q h)

(* Hoare triples *)
type hoare (p:Asrt) (c:stmt) (q:Asrt) : Type =
  (forall st st'. reval c st st' ==> p st ==> q st')

type asrt_sub (x:id) (e:aexp) (p:Asrt) (h:heap) : Type =
       p (update h x (eval_aexp h e))

assume val hoare_asgn : q:Asrt -> x:id -> e:aexp ->
  Lemma (hoare (asrt_sub x e q) (Assign x e) q)

assume val hoare_consequence : p:Asrt -> p':Asrt -> q:Asrt -> q':Asrt -> c:stmt ->
  Lemma (requires (hoare p' c q' /\ asrt_impl p p' /\ asrt_impl q' q))
        (ensures (hoare p c q))

assume val hoare_skip : p:Asrt -> Lemma (hoare p Skip p)

assume val hoare_seq : p:Asrt -> q:Asrt -> r:Asrt -> c1:stmt -> c2:stmt ->
  Lemma (requires (hoare p c1 q /\ hoare q c2 r))
        (ensures (hoare p (Seq c1 c2) q))

type basrt (be:bexp) (h:heap) = (eval_bexp h be = true)

assume val hoare_if : p:Asrt -> q:Asrt -> be:bexp -> t:stmt -> e:stmt ->
  Lemma (requires (hoare (fun h -> p h /\ basrt be h) t q /\
                   hoare (fun h -> p h /\ ~(basrt be h)) e q))
        (ensures (hoare p (Cond be t e) q))

assume val hoare_while : p:Asrt -> be:bexp -> c:stmt ->
  Lemma (requires (hoare (fun h -> p h /\ basrt be h) c p))
        (ensures (hoare p (While be c) (fun h -> p h /\ ~(basrt be h))))


(* Weakest (Liberal) Preconditions *)

(* we can define it directly in F*,
   but this declarative definition not usable in practice
   (this definition is useful for showing completeness though) *)
type wp (c:stmt) (q:Asrt) (h:heap) = (forall h'. reval c h h' ==> q h')

(* Need type level computation to express this
type wlp (c:stmt) (q:Asrt) (h:heap) = ...
- one way to fix this would make to also embed assertions deeply!
- can maybe still give assertions a (Tarski) semantics as a type,
  although that would again require type-level computation
*)
