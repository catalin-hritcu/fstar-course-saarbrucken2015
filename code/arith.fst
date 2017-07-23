module TypedArith 
(*A simple language of arithmetic expressions *)

(* Binary Operators supported by the language *)
type binop =
| Plus : binop
| Minus : binop
| Times : binop
| LT : binop
| GT : binop
| EQ : binop
| Or : binop
| And : binop

(* The language only contains boolean and integer values *)
type value = 
| True : value
| False : value
| Num : i : int -> value

(* Expressions are either constants, if-then-else constructs or an application
of a binary operator *)
type exp =
| Constant : value -> exp
| If : condition: exp -> then_branch: exp -> else_branch: exp -> exp
| BinOp : operator : binop -> op1 : exp -> op2 : exp -> exp 

val step : exp -> Tot (option exp)
let rec step e = match e with
| If c tb eb -> (match c with 
  | Constant True -> Some tb
  | Constant False -> Some eb
  | Constant _ -> None
  | _ -> (match step c with
    | Some c' -> Some (If c' tb eb)
    | None -> None))
| BinOp op op1 op2 -> (match (op1, op2) with 
  | (Constant x, Constant y) -> (match (x,y) with
    | (Num i1, Num i2) -> (match op with
      | Plus -> Some (Constant (Num (i1 + i2)))
      | Minus -> Some (Constant (Num (i1 - i2)))
      | Times -> Some (Constant (Num (i1 * i2)))
      | GT -> Some (Constant (if (i1 > i2) then True else False))
      | LT -> Some (Constant (if (i1 < i2) then True else False))
      | EQ -> Some (Constant (if (i1 = i2) then True else False))
      | _ -> None)
    | (Num _, _) 
    | (_, Num _) -> None
    | _ -> (match op with
      | Or -> (match (x,y) with
        | (False, False) -> Some (Constant False)
        | _ -> Some (Constant True))
      | And -> (match (x,y) with
        | (True, True) -> Some (Constant True)
        | _ -> Some (Constant False))
      | _ -> None))
  | (Constant _, _) -> (match step op2 with
    | Some op2' -> Some (BinOp op op1 op2')
    | None -> None)
  | _ -> (match step op1 with 
    | Some op1' -> Some (BinOp op op1' op2)
    | None -> None))
| _ -> None

(* Expressions can only have type Int or Bool *)
type ty = 
| Int : ty
| Bool : ty

(* mapping from operators to (input_type1 * inputtype2 * outputtype) *)
val typing_op : binop -> Tot (ty * ty * ty)
let typing_op op = match op with 
| Plus 
| Minus 
| Times -> (Int, Int, Int)
| LT  
| GT  
| EQ -> (Int, Int, Bool)
| Or  
| And -> (Bool, Bool, Bool)

(* Typing constants *)
val typing_val : value -> Tot ty 
let typing_val v = match v with
| Num _ -> Int
| _ -> Bool

(* Total type checker with option type *)
val typing : exp -> Tot (option ty)
let rec typing e = match e with 
| Constant v -> Some (typing_val v)
| If b t e -> (match (typing b, typing t, typing e) with
  | (Some Bool, Some t1, Some t2) -> if t1 = t2 then Some t1 else None
  | _ -> None)
| BinOp op op1 op2 -> (match (typing_op op, typing op1, typing op2) with
  | ((t1, t2, tr), Some t1', Some t2') -> if (t1 = t1' && t2 = t2') then 
      Some tr else None
  | _ -> None)

(* progress property *)
val progress : e:exp{is_Some (typing e)} -> Lemma
    (is_Constant e \/ is_Some (step e))
let rec progress e = match e with 
| Constant _ -> ()
| If b t e -> progress b
| BinOp _ op1 op2 -> progress op1; progress op2

(* preservation propoerty *)
val preservation : e:exp{is_Some (typing e) /\ is_Some (step e)} -> Lemma
    (typing (Some.v (step e)) = typing e) 
let rec preservation e = match e with
| If b t e -> if not (is_Constant b) then preservation b
| BinOp op op1 op2 -> match op1, op2 with
  | Constant _, Constant _ -> ()
  | Constant _, _ -> preservation op2
  | _, _ -> preservation op1
