module SimplerWhile
open Expressions

type stmt = 
| Skip   : stmt
| Assign : var:id -> term:aexp -> stmt
| Seq    : first:stmt -> second:stmt -> stmt
| Cond   : cond:bexp -> then_branch:stmt -> else_branch:stmt -> stmt
| While  : cond:bexp -> body:stmt -> stmt 

val update : heap -> id -> int -> Tot heap 
let update h x v = fun y -> if y = x then v else h y

val eval : heap -> stmt -> Dv heap
let rec eval h s =
  match s with
  | Skip -> h
  | Assign x e -> update h x (eval_aexp h e)
  | Seq s1 s2 -> eval (eval h s1) s2
  | Cond be st se -> eval h (if (eval_bexp h be) then st else se)
  | While be sb -> if eval_bexp h be then eval (eval h sb) s else h

assume type reval : stmt -> heap -> heap -> Type
