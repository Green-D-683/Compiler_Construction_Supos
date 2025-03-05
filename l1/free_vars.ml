open Ast 

let rec inlist x = function 
  | [] ->  false 
  | y :: rest -> if x = y then true else inlist x rest 

(* free_vars (bvars, e) returns a 
    list, with no duplicates, of all free variables 
    of e that are not in the list bvars. 
*) 
let free_vars(bvars, exp) = 
    let rec aux bound free = function 
    | UnaryOp(_, e)      -> aux bound free e
    | Op(e1, _, e2)      -> aux bound (aux bound free e1) e2
    | Seq []             -> free 
    | Seq (e :: rest)    -> aux bound (aux bound free e) (Seq rest) 
    | _                  -> free 
   in aux bvars [] exp 

