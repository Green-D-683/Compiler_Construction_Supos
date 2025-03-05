
type var = string 

type oper = ADD | MUL | DIV | SUB

type unary_oper = NEG

type expr = 
       | Integer of int
       | UnaryOp of unary_oper * expr
       | Op of expr * oper * expr
       | Seq of (expr list)

(* printing *) 
val string_of_unary_oper : unary_oper -> string 
val string_of_oper : oper -> string 
val string_of_uop : unary_oper -> string 
val string_of_bop : oper -> string 
val print_expr : expr -> unit 
val eprint_expr : expr -> unit
val string_of_expr : expr -> string 
