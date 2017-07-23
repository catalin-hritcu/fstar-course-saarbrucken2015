
module StlcStrongSub

open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* STLC with subtyping *)

type typ =
  | TArr : typ -> typ -> typ
  | TInt : typ
  | TNat : typ

type var = nat

type exp =
  | EVar : var -> exp
  | EApp : exp -> exp -> exp
  | ELam : typ -> exp -> exp
  | EInt : int -> exp

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

type sub = var -> Tot exp

opaque type renaming (s:sub) = (forall (x:var). is_EVar (s x))

val is_renaming : s:sub -> GTot (n:int{  (renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

val sub_inc_above : nat -> var -> Tot exp
let sub_inc_above n y = if y<n then EVar y else EVar (y+1)

val sub_inc : var -> Tot exp
let sub_inc x = sub_inc_above 0 x

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if is_EVar e then 0 else 1

val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ is_EVar e) ==> is_EVar e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst s e =
  match e with
  | EInt i -> EInt i
  | EVar x -> s x

  | ELam t e1 ->
     let subst_elam : y:var -> Tot (e:exp{renaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in ELam t (subst subst_elam e1)

  | EApp e1 e2 -> EApp (subst s e1) (subst s e2)

val subst_elam: s:sub -> Tot sub
let subst_elam s y =
  if y = 0 then EVar y
  else subst sub_inc (s (y-1))

val subst_extensional: s1:sub -> s2:sub{FEq s1 s2} -> e:exp ->
                       Lemma (requires True)
                             (ensures (subst s1 e = subst s2 e))
                             [SMTPat (subst s1 e); SMTPat (subst s2 e)]
let subst_extensional s1 s2 e = ()

(* subst_beta_gen is a generalization of the substitution we do for
   the beta rule, when we've under x binders
   (useful for the substitution lemma) *)
val sub_beta_gen : var -> exp -> Tot sub
let sub_beta_gen x v = fun y -> if y < x then (EVar y)
                                else if y = x then v (* substitute *)
                                else (EVar (y-1))    (* shift -1 *)

val subst_beta_gen : var -> exp -> exp -> Tot exp
let subst_beta_gen x v = subst (sub_beta_gen x v)

let subst_beta = subst_beta_gen 0

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily in inductive form *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst_beta e2 e1)
  | SApp1 : #e1:exp ->
            e2:exp ->
            #e1':exp ->
            step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)
  | SApp2 : e1:exp ->
            #e2:exp ->
            #e2':exp ->
            step e2 e2' ->
            step (EApp e1 e2) (EApp e1 e2')

(* Type system; in inductive form (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

val extend : env -> var -> typ -> Tot env
let extend g x t y = if y < x then g y
                     else if y = x then Some t
                     else g (y-1)

type subtype : typ -> typ -> Type =
  | SubFun : #t1:typ ->
             #t2:typ ->
             #t1':typ ->
             #t2':typ ->
             subtype t1' t1 ->
             subtype t2 t2' ->
             subtype (TArr t1 t2) (TArr t1' t2')
  | SubNat   : subtype TNat TInt
  | SubRefl  : t:typ -> subtype t t
  | SubTrans : #t1:typ ->
               #t2:typ ->
               #t3:typ ->
               subtype t1 t2 ->
               subtype t2 t3 ->
               subtype t1 t3

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
            x:var{is_Some (g x)} ->
            typing g (EVar x) (Some.v (g x))
  | TyLam : #g:env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            typing (extend g 0 t) e1 t' ->
            typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            typing g e1 (TArr t11 t12) ->
            typing g e2 t11 ->
            typing g (EApp e1 e2) t12
  | TySub : #g:env ->
            #e:exp ->
            #t:typ ->
            #t':typ ->
            typing g e t ->
            subtype t t' ->
            typing g e t'
  | TyInt : #g:env ->
             i:int ->
            typing g (EInt i) TInt

(* Progress proof, a bit larger in constructive style *)

val is_value : exp -> Tot bool
let is_value e = is_ELam e || is_EInt e

opaque val subtype_arr_inv : #s:typ -> t1:typ -> t2:typ ->
      h:subtype s (TArr t1 t2) ->
      Tot (cexists (fun s1 -> cexists (fun s2 ->
             cand (subtype t1 s1) (u:(subtype s2 t2){s = TArr s1 s2}))))
          (decreases h)
let rec subtype_arr_inv s t1 t2 h =
  match h with
  | SubFun #s1 #s2 #t1' #t2' h1 h2 -> ExIntro s1 (ExIntro s2 (Conj h1 h2))
  | SubRefl t -> ExIntro t1 (ExIntro t2 (Conj (SubRefl t1) (SubRefl t2)))
  | SubTrans h1 h2 ->
     (let ExIntro s1 aux1 = subtype_arr_inv t1 t2 h2 in
      let ExIntro s2 aux2 = aux1 in
      let Conj h1' h2' = aux2 in
      let ExIntro s1' aux1' = subtype_arr_inv s1 s2 h1 in
      let ExIntro s2' aux2' = aux1' in
      let Conj h1'' h2'' = aux2' in
      ExIntro s1' (ExIntro s2' (Conj (SubTrans h1' h1'') (SubTrans h2'' h2'))))

val abs_canonical : #v:exp -> t1:typ -> t2:typ -> h:typing empty v (TArr t1 t2) ->
                    Lemma (requires (is_value v))
                          (ensures (is_ELam v)) (decreases h)
let rec abs_canonical v t1 t2 h =
  match h with
  | TyLam _ _ -> ()
  | TySub ht hs ->
     (let ExIntro s1 aux1 = subtype_arr_inv t1 t2 hs in
      let ExIntro s2 aux2 = aux1 in
      let Conj hs1 hs2 = aux2 in
      abs_canonical s1 s2 ht)

opaque val progress : #e:exp -> #t:typ -> h:typing empty e t ->
               Pure (cexists (fun e' -> step e e'))
                    (requires (not (is_value e)))
                    (ensures (fun _ -> True)) (decreases h)
let rec progress _ _ h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
     (if is_value e1 then
        (abs_canonical t11 t12 h1;
         let ELam t e1' = e1 in ExIntro (subst_beta e2 e1') (SBeta t e1' e2))
      else (match progress h1 with
            | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1')))
  | TySub ht hs -> progress ht

(* Typing extensional (weaker) and context invariance (stronger) lemmas *)

(* Typing extensional follows directly from functional extensionality
   (it's also a special case of context invariance below) *)

(* CH: couldn't make this opaque, or substitution would fail *)
val typing_extensional : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{FEq g g'} -> Tot (typing g' e t)
let typing_extensional _ _ _ h _ = h

(* Context invariance (actually used in a single place within substitution,
   for in a specific form of weakening when typing variables) *)

val appears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec appears_free_in x e =
  match e with
  | EInt _ -> false
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | ELam _ e1 -> appears_free_in (x+1) e1

opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:var). appears_free_in x e ==> g1 x = g2 x)

opaque val context_invariance : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyLam t_y h1 ->
    TyLam t_y (context_invariance h1 (extend g' 0 t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')
  | TySub ht hs ->
    TySub (context_invariance ht g') hs
  | TyInt i -> TyInt i

(* Lemmas about substitution and shifting bellow lambdas *)

val shift_up_above : nat -> exp -> Tot exp
let shift_up_above n e = subst (sub_inc_above n) e

val shift_up : exp -> Tot exp
let shift_up e = shift_up_above 0 e

val subst_gen_elam : x:var -> v:exp -> t_y:typ -> e':exp -> Lemma
      (ensures (subst_beta_gen x v (ELam t_y e') =
                ELam t_y (subst_beta_gen (x+1) (shift_up v) e')))
let subst_gen_elam x v t_y e' =
  subst_extensional (subst_elam (sub_beta_gen  x              v))
                                (sub_beta_gen (x+1) (shift_up v))  e'

val shift_up_above_lam : n:nat -> t:typ -> e:exp -> Lemma
  (ensures (shift_up_above n (ELam t e) = ELam t (shift_up_above (n+1) e)))
let shift_up_above_lam n t e =
  subst_extensional (subst_elam (sub_inc_above n)) (sub_inc_above (n+1)) e

(* Weakening (or shifting preserves typing) *)

opaque val weakening : x:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
      h:typing g e t -> Tot (typing (extend g x t') (shift_up_above x e) t)
      (decreases h)
let rec weakening n g v t t' h =
  match h with
  | TyVar y -> if y<n then TyVar y else TyVar (y+1)
  | TyLam #g t_y #e' #t'' h21 ->
      (shift_up_above_lam n t_y e';
       let h21 = weakening (n+1) t' h21 in
       TyLam t_y (typing_extensional h21 (extend (extend g n t') 0 t_y)))
  | TyApp h21 h22 -> TyApp (weakening n t' h21) (weakening n t' h22)
  | TySub ht hs -> TySub (weakening n t' ht) hs
  | TyInt i -> TyInt i

(* Substitution preserves typing *)

opaque val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing g v t_x ->
      h2:typing (extend g x t_x) e t ->
      Tot (typing g (subst_beta_gen x v e) t) (decreases h2)
let rec substitution_preserves_typing x e v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if      x=y then h1
     else if y<x then context_invariance h2 g
     else             TyVar (y-1)
  | TyLam #g' t_y #e' #t' h21 ->
     (let h21' = typing_extensional h21 (extend (extend g 0 t_y) (x+1) t_x) in
      let h1' = weakening 0 t_y h1 in
      subst_gen_elam x v t_y e';
      TyLam t_y (substitution_preserves_typing (x+1) h1' h21'))
  | TyApp h21 h22 ->
    (TyApp (substitution_preserves_typing x h1 h21)
           (substitution_preserves_typing x h1 h22))
  | TySub ht hs -> TySub (substitution_preserves_typing x h1 ht) hs
  | TyInt i -> TyInt i

(* Type preservation *)

opaque val abs_inv : #g:env -> t:typ -> e:exp -> t1:typ -> t2:typ ->
      h:typing g (ELam t e) (TArr t1 t2) ->
      Tot (cand (subtype t1 t) (typing (extend g 0 t) e t2)) (decreases h)
let rec abs_inv g t e t1 t2 h =
  match h with
  | TyLam t' h' -> Conj (SubRefl t') h'
  | TySub ht hs ->
     (let ExIntro s1 aux1 = subtype_arr_inv t1 t2 hs in
      let ExIntro s2 aux2 = aux1 in
      let Conj hs1 hs2 = aux2 in
      let Conj ihs iht = abs_inv t e s1 s2 ht in
      Conj (SubTrans hs1 ihs) (TySub iht hs2))

opaque val preservation : #e:exp -> #e':exp -> hs:step e e' ->
                   #g:env -> #t:typ -> ht:(typing g e t) ->
                   Tot (typing g e' t) (decreases ht)
let rec preservation e e' hs g t ht =
  match ht with
  | TyApp #g' #e1 #e2 #t1 #t2 h1 h2 ->
    (match hs with
     | SBeta t e1' e2' ->
        let Conj i1 i2 = abs_inv t e1' t1 t2 h1 in
        substitution_preserves_typing 0 (TySub h2 i1) i2
     | SApp1 e2' hs1   -> TyApp (preservation hs1 h1) h2
     | SApp2 e1' hs2   -> TyApp h1 (preservation hs2 h2))
  | TySub ht' hsub -> TySub (preservation hs ht') hsub
