module Stlc

(*TODO: ex1 : Add a type and expressions for integers and a test for 0 to
 * the Stlc. Uncomment the marked lines and modify the functions and proofs in
 * the remainder of the file accordingly. (1 Point) *)

(*TODO: ex2 : Add a type and expressions for pairs and two projection functions
 * to the Stlc. Uncomment the marked lines and modify the functions and proofs
 * in the remainder of the file accordingly. See Exercise 7b in the FStar
 * Tutorial for more details and some hints (2 Points) *)

(*TODO: ex3 : Add an expressions for recursive let expressions (the to the Stlc.
 * Uncomment the marked lines and modify the functions and proofs in the
 * remainder of the file accordingly. The expressions are of the form
 * let rec (f:t) (x:t') = e     (2 Points) *)

(*TODO challenge: Extend your solution from ex1 with a type TNat for natural
 * numbers as a subtype of TInt. Modify the typing function so that it supports
 * subtyping.
 * Hints : - You may annotate conditionals with a type
 *         - You can encode the subtyping relation as a total function with type
 *             ty -> ty -> Tot bool
 *         - It might be helpful to define a metric on types and to use it for
 *             decreases clauses
 *         - It might be necessary to modify the statements of some of the
 *             Lemmas to take subtyping into account     (2 Bonus Points)*)

type ty =
  | TBool  : ty
(*| TInt   : ty *)                        (* Uncomment this for ex 1*)
(*| TNat   : ty *)                        (* Uncomment this for challenge*)
(*| TPair  ; t1:ty -> t2:ty -> ty *)      (* Uncomment this for ex 2*)
  | TArrow : t1:ty -> t2:ty -> ty


type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : int -> ty -> exp -> exp
  | ETrue  : exp
  | EFalse : exp
(*| Eint   : int -> exp *)                (* Uncomment this for ex 1*)
(*| EIf0   : exp -> exp -> exp -> exp *)  (* Uncomment this for ex 1*)
  | EIf    : exp -> exp -> exp -> exp
(*| EPair  : exp -> exp -> exp *)         (* Uncomment this for ex 2*)
(*| EFst   : exp -> exp *)                (* Uncomment this for ex 2*)
(*| ESnd   : exp -> exp *)                (* Uncomment this for ex 2*)
(*| ELetR  : int -> ty -> int -> ty -> exp -> exp *) (* Uncomment this for ex 3*)

val is_value : exp -> Tot bool
let rec is_value e =
  match e with
  | EAbs _ _ _
  | ETrue
  | EFalse      -> true
  | _           -> false

(* Because we only consider call-by-value reduction, we will ever only
   substitute closed values, so this definition of substitution is
   good enough *)
val subst : int -> exp -> exp -> Tot exp
let rec subst x e e' =
  match e' with
  | EVar x' -> if x = x' then e else e'
  | EAbs x' t e1 ->
      EAbs x' t (if x = x' then e1 else (subst x e e1))
  | EApp e1 e2 -> EApp (subst x e e1) (subst x e e2)
  | ETrue -> ETrue
  | EFalse -> EFalse
  | EIf e1 e2 e3 -> EIf (subst x e e1) (subst x e e2) (subst x e e3)

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs x t e' -> Some (subst x e2 e')
          | _           -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | EIf e1 e2 e3 ->
      if is_value e1 then
        match e1 with
        | ETrue   -> Some e2
        | EFalse  -> Some e3
        | _       -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EIf e1' e2 e3)
        | None     -> None)
  | _ -> None

type env = int -> Tot (option ty)

val empty : env
let empty _ = None

val extend : env -> int -> ty -> Tot env
let extend g x t x' = if x = x' then Some t else g x'

val typing : env -> exp -> Tot (option ty)
let rec typing g e =
  match e with
  | EVar x -> g x
  | EAbs x t e1 ->
      (match typing (extend g x t) e1 with
      | Some t' -> Some (TArrow t t')
      | None    -> None)
  | EApp e1 e2 ->
      (match typing g e1, typing g e2 with
      | Some (TArrow t11 t12), Some t2 -> if t11 = t2 then Some t12 else None
      | _                    , _       -> None)
  | ETrue
  | EFalse -> Some TBool
  | EIf e1 e2 e3 ->
      (match typing g e1, typing g e2, typing g e3 with
      | Some TBool, Some t2, Some t3 -> if t2 = t3 then Some t2 else None
      | _         , _      , _       -> None)

val progress : e:exp -> Lemma
      (requires (is_Some (typing empty e)))
      (ensures (is_value e \/ (is_Some (step e))))
let rec progress e = by_induction_on e progress

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y _ e1 -> x <> y && appears_free_in x e1
  | EIf e1 e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | ETrue
  | EFalse -> false

val free_in_context : x:int -> e:exp -> g:env -> Lemma
      (requires (is_Some (typing g e)))
      (ensures (appears_free_in x e ==> is_Some (g x)))
let rec free_in_context x e g =
  match e with
  | EVar _
  | ETrue
  | EFalse -> ()
  | EAbs y t e1 -> free_in_context x e1 (extend g y t)
  | EApp e1 e2 -> free_in_context x e1 g; free_in_context x e2 g
  | EIf e1 e2 e3 -> free_in_context x e1 g;
                    free_in_context x e2 g; free_in_context x e3 g

(* Corollary of free_in_context when g=empty -- fed to the SMT solver *)
val typable_empty_closed : x:int -> e:exp -> Lemma
      (requires (is_Some (typing empty e)))
      (ensures (not(appears_free_in x e)))
      [SMTPat (appears_free_in x e)]
let typable_empty_closed x e = free_in_context x e empty

opaque logic type Equal (g1:env) (g2:env) =
                 (forall (x:int). g1 x=g2 x)
opaque logic type EqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:int). appears_free_in x e ==> g1 x=g2 x)

val context_invariance : e:exp -> g:env -> g':env
                     -> Lemma
                          (requires (EqualE e g g'))
                          (ensures (typing g e == typing g' e))
let rec context_invariance e g g' =
  match e with
  | EAbs x t e1 ->
     context_invariance e1 (extend g x t) (extend g' x t)

  | EApp e1 e2 ->
     context_invariance e1 g g';
     context_invariance e2 g g'

  | EIf e1 e2 e3 ->
     context_invariance e1 g g';
     context_invariance e2 g g';
     context_invariance e3 g g'

  | _ -> ()

val typing_extensional : g:env -> g':env -> e:exp
                      -> Lemma
                           (requires (Equal g g'))
                           (ensures (typing g e == typing g' e))
let typing_extensional g g' e = context_invariance e g g'

val substitution_preserves_typing : x:int -> e:exp -> v:exp ->
      g:env{is_Some (typing empty v) &&
            is_Some (typing (extend g x (Some.v (typing empty v))) e)} ->
      Tot (u:unit{typing g (subst x v e) ==
                  typing (extend g x (Some.v (typing empty v))) e})
let rec substitution_preserves_typing x e v g =
  let Some t_x = typing empty v in
  let gx = extend g x t_x in
  match e with
  | ETrue -> ()
  | EFalse -> ()
  | EVar y ->
     if x=y
     then context_invariance v empty g (* uses lemma typable_empty_closed *)
     else context_invariance e gx g

  | EApp e1 e2 ->
     substitution_preserves_typing x e1 v g;
     substitution_preserves_typing x e2 v g

  | EIf e1 e2 e3 ->
     substitution_preserves_typing x e1 v g;
     substitution_preserves_typing x e2 v g;
     substitution_preserves_typing x e3 v g

  | EAbs y t_y e1 ->
     let gxy = extend gx y t_y in
     let gy = extend g y t_y in
     if x=y
     then typing_extensional gxy gy e1
     else
       (let gyx = extend gy x t_x in
        typing_extensional gxy gyx e1;
        substitution_preserves_typing x e1 v gy)

val preservation : e:exp{is_Some (typing empty e) /\ is_Some (step e)} ->
      Tot (u:unit{typing empty (Some.v (step e)) == typing empty e})
let rec preservation e =
  match e with
  | EApp e1 e2 ->
     if is_value e1
     then (if is_value e2
           then let EAbs x _ ebody = e1 in
                substitution_preserves_typing x ebody e2 empty
           else preservation e2)
     else preservation e1

  | EIf e1 _ _ ->
      if is_value e1 then ()
      else preservation e1
