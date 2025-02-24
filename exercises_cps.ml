(* 

Compiler Construction 
Computer Laboratory 
University of Cambridge 
Timothy G. Griffin (tgg22@cam.ac.uk) 

Exercise Set 2. 

Completed by: Daniel Green (dg683@cam.ac.uk)

Topics : 
  a) Replacing tail-recursion with iteration. 
  b) CPS transform 
  c) Defunctionalisation 
*) 


(* Problem 1. 

   Again by hand, eliminate tail recursion from fold_left. 

   Does your source-to-source transformation 
   change the type of the function?  If so, 
   can you rewrite your code so that the type does not change? 

*) 

(* fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a *) 
let rec fold_left f accu l =
  match l with
  |   [] -> accu
  | a::l -> fold_left f (f accu a) l


(* sum up a list *) 

let fold_test f = f (+) 0 [1;2;3;4;5;6;7;8;9;10] 

let sum1 = fold_test fold_left

(*fold_left is already tail resursive, but not in CPS, therefore, must convert to CPS?*)

(*
let rec fold_left_named f accu l = match l with
  | [] -> accu
  | a::l -> let x = fold_left_named f (f accu a) l in x

let rec fold_left_cps f l k = match l with
  | [] -> k 
  | a::l -> fold_left_cps f l (fun x -> f (k a) x)

(+) 0 [1;2;3]
(+) [1;2;3] (fun x -> 0 + x)
(+) [2;3] (fun x` -> ((fun x -> 0 + x) 1) + x`)
(+) [2;3] (fun x` -> (0 + 1) + x`)
(+) [3] (fun x`` -> ((fun x` -> ((fun x -> 0 + x) 1) + x`) 2) + x``)
(+) [3] (fun x`` -> ((0 + 1) + 2) + x``)
(+) [] (fun x``` -> ((fun x`` -> ((fun x` -> ((fun x -> 0 + x) 1) + x`) 2) + x``) 3) + x```)
(+) [] (fun x``` -> (((0 + 1) + 2) + 3) + x```)
One too many fun statements - try use different k
*)

let rec fold_left_cps f accu l k = 
  match l with
  | [] -> k accu
  | a::l -> fold_left_cps f accu l (fun x -> f (k x) a) (*f (k a) x; f x (k a)*)

(* Example Call:
(+) 0 [1;2] (fun x->x)
(+) 0 [2] (fun x` -> ((fun x->x) x') + 1)
(+) 0 [2] (fun x` -> x` + 1)
(+) 0 [] (fun x`` -> ((fun x` -> ((fun x->x) x') + 1) x``) + 2)
(+) 0 [] (fun x`` -> (x`` + 1) + 2)
(fun x`` -> ((fun x` -> ((fun x->x) x') + 1) x``) + 2) 0
(fun x`` -> (x`` + 1) + 2) 0
(0 + 1) + 2
*)

let fold_left_1 f accu l = fold_left_cps f accu l (fun x->x)

(* Thinking through factorial as another naturally tail recursive function
let rec fact_t x acc = match x with
  | 0 -> acc
  | x -> fact_t (x-1) (acc*m)

let rec fact_cps x k = match x with
  | 0 -> k 1
  | x -> fact_cps (x-1) (fun n -> k (x*n))

3 (fun n->n)
2 (fun n`->(fun n->n) (3*n`))
2 (fun n`->3*n`)
1 (fun n``->(fun n`->(fun n->n) (3*n`)) (2*n``))
1 (fun n``->3*(2*n``))
0 (fun n```->(fun n``->(fun n`->(fun n->n) (3*n`)) (2*n``)) (1*n```))
0 (fun n```->3*(2*(1*n```)))
(fun n```->(fun n``->(fun n`->(fun n->n) (3*n`)) (2*n``)) (1*n```)) 1
(fun n```->3*(2*(1*n```))) 1
(3*(2*(1*1))) 
*)

(*1. add constructor for each `fun`*)
type cont = ID | F of int * cont

let rec apply_cont k f accu = match (k, accu) with
  | ID, accu -> accu 
  | F (a, k), accu -> apply_cont k f (f accu a)
and fold_left_defun f accu l k = match l with
  | [] -> apply_cont k f accu
  | a::l -> fold_left_defun f accu l (F (a, k))

let fold_left_2 f accu l = fold_left_defun f accu l ID

let sum2 = fold_test fold_left_2

(*
Feedback:

You’re not quite right with this one. Remember that CPS makes any recursive function tail recursive, but the question is asking us to remove tail recursion.

We can discuss an approach to this in the supo if you like?

*)

(* Problem 2. 

   Apply (by hand) the CPS transformation to 
   the gcd code. 

   Explain your results. 

*) 

let rec gcd(m, n) = 
    if m = n 
    then m 
    else if m < n 
         then gcd(m, n - m)
         else gcd(m - n, n)

let gcd_test f = List.map f [(24, 638); (17, 289); (31, 1889)]

let gcd_test_0 = gcd_test gcd  

(*Name Intermediate Function Calls*)
let rec gcd_named(m,n) = 
  if m = n then m
  else if m < n then let a = gcd(m, n-m) in a
  else let b = gcd(m-n,m) in b

(*Add continuation parameter*)
let rec gcd_cps(m,n) k = 
  if m=n then k m (*Apply Continutation to return values*)
  else if m < n then gcd_cps (m, n-m) (fun a -> k a) (*In recursive calls, append result to continuation*)
  else gcd_cps (m-n,n) (fun b -> k b)

let gcd_1 (m,n) = gcd_cps (m,n) (fun x->x) (*Use identity as base continuation*)

(* GCD is already a tail-recursive problem, so the general approach above can be simplified to just passing `k` instead of `(fun a -> k a)` at each stage *)

let gcd_test_1 = gcd_test gcd_1

(* let () = List.iter (fun x -> Printf.printf "%i " x) (gcd_test_1 @ gcd_test_2) *)

(*
Feedback:

Correct! And good to recognise that you can just pass k back to each gcd_cps call rather than (fun a -> k a).

*)

(* Problem 3. 

Environments are treated as function in interp_0.ml. 

Can you transform these definitions, starting 
with defunctionalisation, and arrive at a list-based
implementation of environments? 
*) 


(* update : ('a -> 'b) * ('a * 'b) -> 'a -> 'b *) 
let update (env, (x, v)) = fun y -> if x = y then v else env y

(* mupdate : ('a -> 'b) * ('a * 'b) list -> 'a -> 'b *) 
let rec mupdate (env, bl) = match bl with 
  | [] -> env 
  | (x, v) :: rest -> mupdate(update(env, (x, v)), rest)

(* env_empty : string -> 'a *) 
let env_empty = fun y -> failwith (y ^ " is not defined!\n")

(* env_init : (string * 'a) list -> string -> 'a *) 
let env_init bl = mupdate(env_empty, bl) 

(* Defunctionalise: *)

type 'a env_cont = UPDATE of 'a env_cont * (string * 'a) | EMPTY

let rec apply_cont_env env y = match (env, y) with
  | EMPTY, y -> failwith (y ^ "is not defined!\n")
  | UPDATE (env, (x, v)), y -> if x = y then v else apply_cont_env env y
and mupdate_defun (env, bl)= match bl with
  | [] -> apply_cont_env env
  | (x, v) :: rest -> mupdate_defun(UPDATE(env, (x, v)), rest)

let env_init_1 bl = mupdate_defun(EMPTY, bl)

(* Build List Implementation *)

type 'a env_tag = UPDATE_TAG of string * 'a
type 'a env_cont_l = 'a env_tag list

let rec apply_cont_env_tag env y = match env, y with
  | [], y -> failwith (y ^ "is not defined!\n")
  | UPDATE_TAG (x, v)::env, y -> if x = y then v else apply_cont_env_tag env y
and mupdate_defun_tag (env, bl) = match bl with
  | [] -> apply_cont_env_tag env
  | (x,v)::rest -> mupdate_defun_tag (((UPDATE_TAG (x,v))::env), rest)

let env_init_2 bl = mupdate_defun_tag ([], bl) (* List Continuations, as required *)


(*
Feedback:

Spot on.

*)

(* Problem 4. 

   Below is the code for (uncurried) map, with an test using fib. 
   Can you apply the CPS transformation to map to produce map_cps? 
   Will this map_cps still work with fib?  If not, what to do? 

*) 

(* map : ('a -> 'b) * 'a list -> 'b list *) 
let rec map(f, l) = 
    match l with 
    | [] -> [] 
    | a :: rest -> (f a) :: (map(f, rest)) 

(* fib : int -> int *) 
let rec fib m =
    if m = 0 
    then 1 
    else if m = 1 
         then 1 
         else fib(m - 1) + fib (m - 2) 

let map_test f = f (fib, [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10])

let map_test_1 = map_test map

let rec map_named (f, l) = 
  match l with
  | [] -> []
  | a :: rest ->  let x = f a in
                  let xs = map(f, rest) in 
                  x::xs
                  
let rec map_cps (f, l) k = 
  match l with
  | [] -> k []
  | a::rest -> map_cps (f, rest) (fun x -> k ((f a)::x)) (*This seems to still work with `fib`, I think?*)

let map_1 (f, l) = map_cps (f, l) (fun x->x)

let map_test_2 = map_test map_1


(*
Feedback:

You’re not quite there with this one – there's something else that you need to do. I don’t want to spoil it ahead of the supo but take another look and see if you can spot what else is required?

*)

let printi x = Printf.printf "%i " x
let print_qnum x = Printf.printf "%i)\n" x
let newl = function _ -> print_endline ""

let printlist xs = List.iter printi xs; newl ()

let printq_i q t1 t2 = print_qnum q; printlist [t1]; printlist [t2]; newl ()
let printq_l q t1 t2 = print_qnum q; printlist t1; printlist t2; newl ()

let () =  printq_i 1 sum1 sum2;
          printq_l 2 gcd_test_0 gcd_test_1; 
          printq_l 4 map_test_1 map_test_2