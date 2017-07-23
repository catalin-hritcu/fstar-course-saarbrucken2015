module StlcWithSubtyping

type ty =
  | TInt : ty
  | TNat : ty
  | TArrow : t1:ty -> t2:ty -> ty

type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : int -> ty -> exp -> exp
  | EInt   : int -> exp
  | EIf0    : exp -> ty -> exp -> exp -> exp

val is_value : exp -> Tot bool
let rec is_value e =
  match e with
  | EAbs _ _ _  -> true
  | EInt n      -> true
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
  | EInt _ -> e'
  | EIf0 e1 t e2 e3 -> EIf0 (subst x e e1) t (subst x e e2) (subst x e e3)

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
  | EIf0 e1 t e2 e3 ->
      if is_value e1 then
        match e1 with
        | EInt 0   -> Some e2
        | EInt n  -> Some e3
        | _       -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EIf0 e1' t e2 e3)
        | None     -> None)
  | _ -> None

type env = int -> Tot (option ty)

val empty : env
let empty _ = None

val extend : env -> int -> ty -> Tot env
let extend g x t x' = if x = x' then Some t else g x'

val type_size : ty -> Tot nat
let rec type_size t = match t with 
| TNat -> 0
| TInt -> 0
| TArrow t1 t2 -> 1 + type_size t1 + type_size t2 

val is_subtype : t1 : ty -> t2 : ty -> Tot bool (decreases (type_size t1 + type_size t2))
let rec is_subtype t1 t2 = 
if t1=t2 then true else 
match t1,t2 with
| TNat,TInt -> true
| TArrow t1' t1'', TArrow t2' t2'' -> (is_subtype t2' t1' && is_subtype t1'' t2'')
| _ -> false

val subtype_transitive : t1 : ty -> t2 : ty -> t3 : ty -> Lemma
(requires (is_subtype t1 t2 && is_subtype t2 t3)) (ensures (is_subtype t1 t3)) (decreases (type_size t1 + type_size t2 + type_size t3))
let rec subtype_transitive t1 t2 t3 = 
if t1=t2 then () else if t2 = t3 then () else
match t1 with
| TArrow t1' t1'' -> let TArrow t2' t2'' = t2 in
let TArrow t3' t3'' = t3 in (subtype_transitive t3' t2' t1'; subtype_transitive t1'' t2'' t3'')
| TNat -> ()
| TInt -> ()


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
      | Some (TArrow t11 t12), Some t2 -> if is_subtype t2 t11 then Some t12 else None
      | _                    , _       -> None)
  | EInt n -> if n >= 0 then Some TNat else Some TInt
  | EIf0 e1 t e2 e3 ->
      (match typing g e1, typing g e2, typing g e3 with
      | Some t1, Some t2, Some t3 -> if is_subtype t1 TInt && is_subtype t2 t && is_subtype t3 t then Some t else None
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
  | EIf0 e1 t e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | EInt n -> false

val free_in_context : x:int -> e:exp -> g:env -> Lemma
      (requires (is_Some (typing g e)))
      (ensures (appears_free_in x e ==> is_Some (g x)))
let rec free_in_context x e g =
  match e with
  | EVar _ -> ()
  | EInt n -> ()
  | EAbs y t e1 -> free_in_context x e1 (extend g y t)
  | EApp e1 e2 -> free_in_context x e1 g; free_in_context x e2 g
  | EIf0 e1 t e2 e3 -> free_in_context x e1 g;
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

  | EIf0 e1 t e2 e3 ->
     context_invariance e1 g g';
     context_invariance e2 g g';
     context_invariance e3 g g'

  | _ -> ()




val typing_extensional : g:env -> g':env -> e:exp
                      -> Lemma
                           (requires (Equal g g'))
                           (ensures (typing g e == typing g' e))
let typing_extensional g g' e = context_invariance e g g'

val substitution_preserves_typing : x:int -> e:exp -> v:exp -> t : ty ->
      g:env{is_Some (typing empty v) &&
            is_Some (typing (extend g x t) e) && is_subtype (Some.v (typing empty v)) t } -> (*is_Some (typing gx e) *)
      Tot (u:unit{is_Some (typing g (subst x v e)) && is_subtype (Some.v (typing g (subst x v e))) 
                  (Some.v (typing (extend g x t) e))}) (*is_subtype (typing g v[x->e]) (typing gx e) *)(decreases e)
let rec substitution_preserves_typing x e v t g =
  let Some t_x = typing empty v in
  let gx = extend g x t in
  match e with
  | EInt _ -> ()
  | EVar y ->
     if x=y
     then context_invariance v empty g (* uses lemma typable_empty_closed *)
     else context_invariance e gx g

  | EApp e1 e2 ->
     substitution_preserves_typing x e1 v t g; (*is_Some (typing gx (App e1 e2)) /\ is_Some (typing g e1[x -> v]) /\ is_Some (typing g e2[x -> v]) *)
     assert (is_TArrow (Some.v (typing g (subst x v e1))));
     let Some (TArrow t11 t12) = typing g (subst x v e1) in
     let Some (TArrow t11' t12') = typing gx e1 in
     assert(is_subtype t11' t11); 
     assert(is_subtype t12 t12');
     substitution_preserves_typing x e2 v t g;
     let Some t2 = typing g (subst x v e2) in
     let Some t2' = typing gx e2 in
     assert(is_subtype t2 t2');
     assert(is_subtype t2' t11');
     subtype_transitive t2 t2' t11';
     subtype_transitive t2 t11' t11

  | EIf0 e1 t' e2 e3 ->
     substitution_preserves_typing x e1 v t g;
     substitution_preserves_typing x e2 v t g;
     substitution_preserves_typing x e3 v t g;
     let Some t2 = typing g (subst x v e2) in
     let Some t2' = typing gx e2 in
     let Some t3 = typing g (subst x v e3) in
     let Some t3' = typing gx e3 in
     subtype_transitive t2 t2' t';
     subtype_transitive t3 t3' t'

  | EAbs y t_y e1 ->
     let gxy = extend gx y t_y in
     let gy = extend g y t_y in
     if x=y
     then typing_extensional gxy gy e1
     else
       (let gyx = extend gy x t in
        typing_extensional gxy gyx e1;
        substitution_preserves_typing x e1 v t gy);
	assert(is_Some (typing g (subst x v e)))

val preservation : e:exp{is_Some (typing empty e) /\ is_Some (step e)} ->
      Tot (u:unit{is_Some (typing empty (Some.v (step e))) /\is_subtype (Some.v (typing empty (Some.v (step e)))) (Some.v (typing empty e))})
let rec preservation e =
  match e with
  | EApp e1 e2 ->
     let Some (TArrow t11 t12), Some t2 = typing empty e1, typing empty e2 in
     assert (is_subtype t2 t11);
     if is_value e1
     then (if is_value e2
           then 
let EAbs x t ebody = e1 in
                substitution_preserves_typing x ebody e2 t empty
           else (preservation e2; let Some t2' = typing empty (Some.v (step e2)) in subtype_transitive t2' t2 t11))
     else (preservation e1; let Some (TArrow t11' t12') = typing empty (Some.v (step e1)) in subtype_transitive t2 t11 t11') (* Here, the thing to prove is that if typing empty e : t1 -> t2, and e' = step (e) then
typing empty e' : t1 -> t2'. This should be ok since the t1 comes from a lambda, which is annotated and this annotation
cannot be changed by a reduction *)

  | EIf0 e1 _ _ _ ->
      if is_value e1 then ()
      else preservation e1
