module StlcStrongSimpleState

open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* STLC with simple state *)

(* TODO do the proofs of progress and preservation below. You may base
        your proofs on the STLC code presented in the lecture.*)

type tcon =
  | TCInt  : tcon
  | TCUnit : tcon
  | TCRefI : tcon

type typ =
  | TArr : typ -> typ -> typ
  | TCon : tcon -> typ

type var = nat

type ref = nat

type econ =
  | CInt   : int -> econ
  | CRef   : ref -> econ
  | CRead  : econ
  | CWrite : econ
  | CUnit  : econ

type exp =
  | EVar : var  -> exp
  | EApp : exp  -> exp -> exp
  | ELam : typ  -> exp -> exp
  | ECon : econ -> exp

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
  | EVar x -> s x

  | ELam t e1 ->
     let subst_elam : y:var -> Tot (e:exp{renaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in ELam t (subst subst_elam e1)

  | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
  | _ -> e

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

type heap = ref -> Tot int
val heap_upd : heap -> ref -> int -> Tot heap
let heap_upd h r i = fun r' -> if r = r' then i else h r'

type config = 
  | Cfg : h:heap -> e:exp -> config

type step : config -> config -> Type =
  | SBeta : t:typ ->
            h:heap ->
            e1:exp ->
            e2:exp ->
            step (Cfg h (EApp (ELam t e1) e2)) (Cfg h (subst_beta e2 e1))
  | SApp1 : #h:heap ->
            #e1:exp ->
            #h':heap ->
            e2:exp ->
            #e1':exp ->
            step (Cfg h e1) (Cfg h' e1') ->
            step (Cfg h (EApp e1 e2)) (Cfg h' (EApp e1' e2))
  | SApp2 : #h:heap ->
            e1:exp ->
            #h':heap ->
            #e2:exp ->
            #e2':exp ->
            step (Cfg h e2) (Cfg h' e2') ->
            step (Cfg h (EApp e1 e2)) (Cfg h' (EApp e1 e2'))
  | SRead : h:heap ->
            r:ref ->
            step (Cfg h (EApp (ECon CRead) (ECon (CRef r))))
                 (Cfg h (ECon (CInt (h r))))
  | SWrite : h:heap ->
             r:ref ->
             i:int ->
             step (Cfg h (EApp (EApp (ECon CWrite) (ECon (CRef r))) (ECon (CInt i))))
                  (Cfg (heap_upd h r i) (ECon CUnit))

(* Type system; in inductive form (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

val extend : env -> var -> typ -> Tot env
let extend g x t y = if y < x then g y
                     else if y = x then Some t
                     else g (y-1)

val type_con : econ -> Tot typ
let type_con c =
  match c with
  | CInt _ -> TCon TCInt
  | CRef _ -> TCon TCRefI
  | CRead  -> TArr (TCon TCRefI) (TCon TCInt)
  | CWrite -> TArr (TCon TCRefI) (TArr (TCon TCInt) (TCon TCUnit))
  | CUnit  -> TCon TCUnit

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
  | TyCon : #g:env ->
            c:econ ->
            typing g (ECon c) (type_con c)

(* Progress proof, a bit larger in constructive style *)

val is_value : exp -> Tot bool
let is_value e = 
  match e with
  | ELam _ _
  | ECon _
  | EApp (ECon CWrite) (ECon (CRef _)) -> true
  | _                                  -> false

val progress : he:heap -> e:exp{not (is_value e)} -> #t:typ ->
               h:typing empty e t ->
               Tot (cexists (fun c -> step (Cfg he e) c)) (decreases h)

(* Typing extensional (weaker) and context invariance (stronger) lemmas *)

(* Typing extensional follows directly from functional extensionality
   (it's also a special case of context invariance below) *)

val typing_extensional : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{FEq g g'} -> Tot (typing g' e t)
let typing_extensional _ _ _ h _ = h

(* Context invariance (actually used in a single place within substitution,
   for in a specific form of weakening when typing variables) *)

val appears_free_in : x:var -> e:exp -> Tot bool (decreases e)
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | ELam _ e1 -> appears_free_in (x+1) e1
  | _ -> false

opaque logic type EnvEqualE (e:exp) (g1:env) (g2:env) =
                 (forall (x:var). appears_free_in x e ==> g1 x = g2 x)

val context_invariance : #e:exp -> #g:env -> #t:typ ->
      h:(typing g e t) -> g':env{EnvEqualE e g g'} ->
      Tot (typing g' e t) (decreases h)
let rec context_invariance _ _ _ h g' =
  match h with
  | TyVar x -> TyVar x
  | TyLam t_y h1 ->
    TyLam t_y (context_invariance h1 (extend g' 0 t_y))
  | TyApp h1 h2 ->
    TyApp (context_invariance h1 g') (context_invariance h2 g')
  | TyCon c -> TyCon c

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

val weakening : x:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
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
  | TyCon c -> TyCon c

(* Substitution preserves typing *)

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:typ -> #t:typ -> #g:env ->
      h1:typing g v t_x ->
      h2:typing (extend g x t_x) e t ->
      Tot (typing g (subst_beta_gen x v e) t) (decreases e)
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
  | TyCon c -> TyCon c

(* Type preservation *)

val preservation : #c:config -> #c':config ->
                   hs:step c c' ->
                   #g:env -> #t:typ -> ht:(typing g (Cfg.e c) t) ->
                   Tot (typing g (Cfg.e c') t) (decreases ht)
