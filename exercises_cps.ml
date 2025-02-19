(* 

Compiler Construction 
Computer Laboratory 
University of Cambridge 
Timothy G. Griffin (tgg22@cam.ac.uk) 

Exercise Set 2. 

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
      [] -> accu
  | a::l -> fold_left f (f accu a) l


(* sum up a list *) 
let sum1 = fold_left (+) 0 [1;2;3;4;5;6;7;8;9;10]  


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

let gcd_test_1 = List.map gcd [(24, 638); (17, 289); (31, 1889)] 



(* Problem 3. 

Environments are treated as function in interp_0.ml. 

Can you transform these definitions, starting 
with defunctionalisation, and arrive at a list-based
implementation of environments? 
*) 


(* update : ('a -> 'b) * ('a * 'b) -> 'a -> 'b *) 
let update(env, (x, v)) = fun y -> if x = y then v else env y

(* mupdate : ('a -> 'b) * ('a * 'b) list -> 'a -> 'b *) 
let rec mupdate(env, bl) = 
    match bl with 
    | [] -> env 
    | (x, v) :: rest -> mupdate(update(env, (x, v)), rest)

(* env_empty : string -> 'a *) 
let env_empty = fun y -> failwith (y ^ " is not defined!\n")

(* env_init : (string * 'a) list -> string -> 'a *) 
let env_init bl = mupdate(env_empty, bl) 


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

let map_test_1 = map(fib, [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10])


