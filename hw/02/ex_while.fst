module While

(* binary operators *)
type binop =
| Plus
| Minus
| Times
| Lt
| Gt
| Eq
| Or
| And

(* identifiers for variables *)
type id = nat

(* values (just constants) *)
type value = 
| VBool : bool -> value
| VInt  : int  -> value

(* arithmetic expressions *)
type exp =
| Val : value -> exp
| Var : id -> exp 
| If  : condition:exp -> then_branch:exp -> else_branch:exp -> exp
| Op  : binop -> exp -> exp -> exp 


(* TODO: extend the type stmt with a constructor for conditionals and modify all 
 * affected functions so that they support the newly introduced conditionals *)

(* statements *)
type stmt = 
| Skip   : stmt
| Assign : var:id -> term:exp -> stmt
| Seq    : first:stmt -> second:stmt -> stmt
(* | Cond   : cond:exp -> then_branch:stmt -> else_branch:stmt -> stmt *)
| While  : cond:exp -> body:stmt -> stmt 

(* types *)
type typ = 
| TInt  : typ
| TBool : typ

(* heaps *)
type heap = id -> Tot value

(* updating the heap *)
val update : heap -> id -> value -> Tot heap 
let update h x v = fun y -> if y = x then v else h y

exception TypeError

(* evaluation function for expressions *)
val eval_exp : heap -> exp -> Ex value
let rec eval_exp h e =
  match e with 
  | Val v -> v
  | Var x -> h x
  | If c t e ->
     (match eval_exp h c with
      | VBool b -> eval_exp h (if b then t else e)
      | _       -> raise TypeError)
  | Op op op1 op2 ->
     (match eval_exp h op1, eval_exp h op2 with
      | VInt i1, VInt i2 ->
         (match op with
          | Plus  -> VInt  (i1 + i2)
          | Minus -> VInt  (i1 - i2)
          | Times -> VInt  (i1 * i2)
          | Gt    -> VBool (i1 > i2)
          | Lt    -> VBool (i1 < i2)
          | Eq    -> VBool (i1 = i2)
          | _     -> raise TypeError)
      | VBool b1, VBool b2 ->
         (match op with
          | Or  -> VBool (b1 || b2)
          | And -> VBool (b1 && b2)
          | _   -> raise TypeError)
      | _ -> raise TypeError)

(* evaluation function for statements *)
val eval : heap -> stmt -> Ex heap (* Remember: Ex includes Div! *)
let rec eval h s =
  match s with
  | Skip -> h
  | Assign x t -> update h x (eval_exp h t)
  | Seq s1 s2 -> eval (eval h s1) s2
  | While c b ->
    (match eval_exp h c with 
    | VBool true  -> eval (eval h b) s
    | VBool false -> h
    | _           -> raise TypeError)

(* mapping from operators to (input_type1 * inputtype2 * outputtype) *)
val op_type : binop -> Tot (typ * typ * typ)
let op_type op =
  match op with 
  | Plus 
  | Minus 
  | Times -> (TInt , TInt , TInt )
  | Lt  
  | Gt  
  | Eq    -> (TInt , TInt , TBool)
  | Or  
  | And   -> (TBool, TBool, TBool)

(* Typing constants *)
val typecheck_val : value -> Tot typ 
let typecheck_val v =
  match v with
  | VInt  _ -> TInt
  | VBool _ -> TBool

(* Type environments *)
type env  = id -> Tot typ

(* Type checker for arithmetic expressions *)
val typecheck_exp : env ->  exp -> Tot (option typ)
let rec typecheck_exp g e =
  match e with 
  | Val v -> Some (typecheck_val v)
  | Var x -> Some (g x)
  | If c t e ->
     (match typecheck_exp g c, typecheck_exp g t, typecheck_exp g e with
          | Some TBool       , Some t1          , Some t2 -> if t1 = t2
                                                             then Some t1
                                                             else None
          | _                            -> None)
  | Op op op1 op2 ->
     (match op_type op  , typecheck_exp g op1, typecheck_exp g op2 with
          | (t1, t2, tr), Some t1'           , Some t2' -> if t1 = t1' && t2 = t2'
                                                           then Some tr else None
          | _                                           -> None)

(* Type-checker for stmts *)
val typecheck : env -> stmt -> Tot bool
let rec typecheck g s =
  match s with
  | Skip -> true
  | Assign x t ->
     (match typecheck_exp g t with 
      | Some ty -> g x = ty
      | None    -> false)
  | Seq s1 s2 -> typecheck g s1 && typecheck g s2
  | While c s ->
     (match typecheck_exp g c, typecheck g s with 
            | Some TBool     , true          -> true
            | _                              -> false)

(* ensures that type and value environment match *)
type typed_heap (g : env) (h : heap) = (forall x. typecheck_val (h x) = g x)

(* total evaluation function for well typed expressions *)
val eval_exp_tot : g:env ->
                   h:heap{typed_heap g h} ->
                   e:exp{is_Some (typecheck_exp g e)} ->
                   Tot (v:value{typecheck_val v = Some.v (typecheck_exp g e)})
let rec eval_exp_tot g h e =
  match e with
  | Val v -> v
  | Var x -> h x
  | If b t e -> let VBool b = eval_exp_tot g h b in
                eval_exp_tot g h (if b then t else e)
  | Op op op1 op2 ->
     (match eval_exp_tot g h op1, eval_exp_tot g h op2 with
      | VInt i1, VInt i2 ->
         (match op with
          | Plus  -> VInt  (i1 + i2)
          | Minus -> VInt  (i1 - i2)
          | Times -> VInt  (i1 * i2)
          | Gt    -> VBool (i1 > i2)
          | Lt    -> VBool (i1 < i2)
          | Eq    -> VBool (i1 = i2))
      | VBool b1, VBool b2 ->
         (match op with
          | Or  -> VBool (b1 || b2)
          | And -> VBool (b1 && b2)))

(* evaluation function for well typed stmts (may diverge) *)
val eval_div : g:env ->
               h:heap{typed_heap g h} -> 
               s:stmt{typecheck g s}  -> 
               Dv (h':heap{typed_heap g h'})
let rec eval_div g h s =
  match s with
  | Skip -> h
  | Assign x t -> update h x (eval_exp_tot g h t)
  | Seq s1 s2 -> eval_div g (eval_div g h s1) s2 
  | While c s' -> let VBool b = eval_exp_tot g h c in
                  if b then eval_div g (eval_div g h s') s else h

(* TODO: remove While from the file and prove eval_div terminating *)
