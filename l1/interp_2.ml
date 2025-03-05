(**************************************
Compiler Construction 2016
Computer Laboratory 
University of Cambridge 
Timothy G. Griffin (tgg22@cam.ac.uk) 
*****************************************) 
(* Interpreter 2. 

A high-level stack-oriented abstract machine with compiler. 
What do I mean by "high-level"? 
---Code is still tree-structured. 
---Complex values are pushed onto value stack.  
---Slang state (heap) used only for references. 
---Code is maintained on a code stack. 
---Program variables contained in code.
*) 


open Ast 

let complain = Errors.complain

type address = int 

type var = string 

type value = 
     | INT of int 

and closure = code * env 

and instruction = 
  | UNARY of unary_oper   
  | OPER of oper 
  | PUSH of value 
  | POP 

and code = instruction list 

and binding = var * value

and env = binding list

type env_or_value = EV of env | V of value 

type env_value_stack = env_or_value list

(* This is the the slang program state --- that is, values for references *) 
(* It is an array of referenced values together with next unallocated address *)
type state = (value array) * int 

type interp_state = code * env_value_stack * state 

(* Printing *) 

let string_of_list sep f l = 
   let rec aux f = function 
     | [] -> ""
     | [t] -> (f t)
     | t :: rest -> (f t) ^  sep  ^ (aux f rest)
   in "[" ^ (aux f l) ^ "]"

let rec string_of_value = function 
     | INT n          -> string_of_int n 

and string_of_closure (c, env) = 
   "(" ^ (string_of_code c) ^ ", " ^ (string_of_env env) ^ ")"

and string_of_env env = string_of_list ",\n " string_of_binding env 

and string_of_binding (x, v) =    "(" ^ x ^ ", " ^ (string_of_value v) ^ ")"

and string_of_instruction = function 
 | UNARY op     -> "UNARY " ^ (string_of_uop op) 
 | OPER op      -> "OPER " ^ (string_of_bop op) 
 | PUSH v       -> "PUSH " ^ (string_of_value v)  
 | POP          -> "POP"

and string_of_code c = string_of_list ";\n " string_of_instruction c 

let string_of_env_or_value = function 
  | EV env -> "EV " ^ (string_of_env env)
  | V v -> "V " ^ (string_of_value v)

let string_of_env_value_stack = string_of_list ";\n " string_of_env_or_value 

let string_of_state (heap, i)  = 
    let rec aux k = 
            if i < k 
	    then "" 
	    else (string_of_int k) ^ " -> " ^ (string_of_value (heap.(k))) ^ "\n" ^ (aux (k+1)) 
    in if i = 0
       then ""
       else "\nHeap = \n" ^ (aux 0) 

let string_of_interp_state (c, evs, s) = 
     "\nCode Stack = \n" ^ (string_of_code c) 
     ^ "\nEnv/Value Stack = \n" ^ (string_of_env_value_stack evs) 
     ^ (string_of_state(s)) 

(* The "MACHINE" *) 

(* allocate a new location in the heap
   and give it value v
*) 
let allocate (heap, i) v = 
    if i < Option.heap_max 
    then let _ = heap.(i) <- v
         in (i, (heap, i+1))
    else complain "runtime error: heap kaput"

let deref (heap, _) a = heap.(a)

let assign (heap, i) a v =
    let _ = heap.(a) <- v
    in (heap, i) 


(* update : (env * binding) -> env *) 
let update(env, (x, v)) = (x, v) :: env 

 let rec evs_to_env = function 
  | [] -> []
  | (V _) :: rest -> evs_to_env rest 
  | (EV env) :: rest -> env @ (evs_to_env rest) 
    
    
let readint () = let _ = print_string "input> " in read_int() 

let do_unary = function 
  | (NEG,  INT m)  -> INT (-m)
  | (op, _) -> complain ("malformed unary operator: " ^ (string_of_unary_oper op))

let do_oper = function 
  | (ADD,  INT m,   INT n)  -> INT (m + n)
  | (SUB,  INT m,   INT n)  -> INT (m - n)
  | (MUL,  INT m,   INT n)  -> INT (m * n)
  | (DIV,  INT m,   INT n)  -> INT (m / n)
  | (op, _, _)  -> complain ("malformed binary operator: " ^ (string_of_oper op))

(*
    val step : interp_state -> interp_state 
             = (code * env_value_stack * state) -> (code * env_value_stack * state) 
*) 
let step = function 

(* (code stack,         value/env stack, state) -> (code stack,  value/env stack, state) *)  
 | ((PUSH v) :: ds,                        evs, s) -> (ds, (V v) :: evs, s)
 | (POP :: ds,                        e :: evs, s) -> (ds, evs, s) 
 | ((UNARY op) :: ds,             (V v) :: evs, s) -> (ds, V(do_unary(op, v)) :: evs, s) 
 | ((OPER op) :: ds,   (V v2) :: (V v1) :: evs, s) -> (ds, V(do_oper(op, v1, v2)) :: evs, s)

 | state -> complain ("step : bad state = " ^ (string_of_interp_state state) ^ "\n")

let rec driver n state = 
  let _ = if Option.verbose 
          then print_string ("\nState " ^ (string_of_int n) 
                             ^ " : " ^ (string_of_interp_state state) ^ "\n")
          else () 
  in match state with 
     | ([], [V v], s) -> (v, s)  
     | _ -> driver (n + 1) (step state) 


(*
   val compile : expr -> code 
*) 
let rec compile = function 
 | Integer n      -> [PUSH (INT n)] 
 | UnaryOp(op, e) -> (compile e) @ [UNARY op]
 | Op(e1, op, e2) -> (compile e1) @ (compile e2) @ [OPER op] 
 | Seq []         -> [] 
 | Seq [e]        -> compile e
 | Seq (e ::rest) -> (compile e) @ [POP] @ (compile (Seq rest))

(* The initial L1 state is the L1 state : all locations contain 0 *) 

let initial_state  = (Array.make Option.heap_max (INT 0), 0)

let initial_env = [] 

(* interpret : expr -> (value * state) *) 
let interpret e = 
    let c = compile e in 
    let _ = if Option.verbose 
            then print_string("Compile code =\n" ^ (string_of_code c) ^ "\n")
            else () 
    in driver 1 (c, initial_env, initial_state)




    

      
    
    
