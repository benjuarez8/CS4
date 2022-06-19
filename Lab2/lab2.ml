open Num
let ni = num_of_int

(***** PART A: ORDERS OF GROWTH *****)

(* A.1 *)
(*
  The space complexity would be O(n), which is different from the time 
  complexity O(2^n) since we can imagine Ocaml evaluating fib (n - 1) all the 
  way until it is fully evaluated before moving onto fib (n - 2).  With this, 
  the memory is returned before fib (n - 2) is evaluated, so there can only be
  at most n pending operations.  In other words, although there are a lot of 
  operations, they are not stored in memory all at the same time due to 
  applicative-order evaluation.
*)

(* A.2.1 *)
(*
  The function p is applied 5 times when sine 12.15 is evaluated.
*)

(* A.2.2 *)
(*
  The space and time complexity are both O(log(a)).  Solving for n in 
  a/3^n < 0.1 gives us log_3(a/0.1) = log_3(10a) which is essentially the depth
  of the recursive pending operations, thus giving us the space complexity of 
  O(log_3(10a)) = O(log(a)).  This number of pending operations is also the 
  number of total operations, so the time complexity is equivalent to the space
  complexity.
*)

(* A.3.a *)
let rec fast_expt b n =
  let is_even m = m mod 2 = 0 in
  let square m = m * m in
    match n with
      | 0 -> 1
      | n' when is_even n' -> square (fast_expt b (n' / 2))
      | _ -> b * fast_expt b (n - 1)

(* A.3.b *)
let ifast_expt b n = 
  let is_even m = m mod 2 = 0 in
  let square m = m * m in 
  let rec iter a b n = 
    match n with
      | 0 -> a
      | n' when is_even n' -> iter a (square b) (n' / 2) 
      | _ -> iter (a * b) b (n - 1)
  in 
    iter 1 b n

(* A.4 *)
let rec fast_mult a b =
  let double m = m + m in
  let halve m = m / 2 in 
    match b with
      | 0 -> 0
      | b' when b' mod 2 = 0 -> double (fast_mult a (halve b'))
      | _ -> a + fast_mult a (b - 1)

(* A.5 *)
let ifast_mult b n = 
  let is_even m = m mod 2 = 0 in
  let double n = n + n in
  let halve n = n / 2 in 
  let rec iter a b n =
    match n with
      | 0 -> a
      | n' when is_even n' -> iter a (double b) (halve n')
      | _ -> iter (a + b) b (n - 1)
  in 
    iter 0 b n

(* A.6 *)
(*
  Similar to A.1, the first argument (foo f (n / 2)) is fully evaluated before
  moving onto the next (equivalent) argument.  Considering that n is being 
  halved with each call, the recursive tree have a depth of log_2(n).  Knowing 
  that the space complexity is determined by this depth, we have that the space
  complexity is O(log_2(n)) = O(log(n)).  Again, knowing that each foo call 
  corresponds to 2 more foo calls, we determine that the time complexity is O(n)
  since O(2^log_2(n)) = O(n).
*)

(* A.7.1 *)
(*
  This function represents a linear recursive process since there are n + 1 
  recursive calls such that there is a single recursive call in each function 
  call.  We know it is not linear iterative because the process is proportional
  to the size of the input.
*)

(* A.7.2 *)
(*
  Following the argument in A.7.1, the space complexity and time complexity are
  both O(n).
*)

(***** PART B: EVALUATION *****)

(* B.1.a *)
(*
  (fun x y -> x * (2 + y)) 20 (2 * 4)
*)

(* B.1.b *)
(*
  (fun a b c -> sqrt (b *. b -. 4.0 *. a *. c)) 1.0 20.0 3.0
*)

(* B.1.c *)
(*
  (fun x -> (fun y -> (fun z -> x * y * z) 3) 2) 1
*)

(* B.1.d *)
(*
  (fun x -> (fun x -> (fun x -> x * x * x) 3) 2) 1
*)

(* B.2 *)
(*
  Desugar:
  (fun x y -> let y = 14 in let z = 22 in x * y * z) (2 * 10) (3 + 4)
  (fun x y -> (fun y -> let z = 22 in x * y * z) 14) (2 * 10) (3 + 4)
  (fun x y -> (fun y -> (fun z -> x * y * z) 22) 14) (2 * 10) (3 + 4)

  Evaluate fun x y -> ...
    evaluate (2 * 10) -> 20
    evaluate (3 + 4) -> 7
    apply fun x y -> ... to 20 7
      substitute 20 for x, 7 for y in ...
        -> (fun y -> (fun z -> 20 * y * z) 22) 14)
      evaluate fun y -> ...
        apply fun y -> ... to 14
          substitute 14 for y in ...
            -> (fun z -> 20 * 14 * z) 22)
          evaluate fun z -> ...
            apply fun z to 22
              substitute 22 for z in ...
                -> (20 * 14 * 22)
              evaluate (20 * 14 * 22) -> 6160
    Result: 6160
*)

(* B.3 *)
(*
  Desugar:
  (fun x y z -> z + y + z) 10 (x * 2) (y + 3)

  Since the operands are evaluated first, this code won't work because x has not
  been bound to 10 before (x * 2) is being evaluated.  The same goes for y with
  (y + 3).  Thus, Ben has an unbound value error.  Ben could simply fix this
  with the following code:

  let x = 10 in
  let y = x * 10 in
  let z = y + 3 in
    x + y + z
*)

(***** PART C: HIGHER-ORDER FUNCTIONS *****)

(* C.1 *)
let isum term a next b =
  let rec iter a result =
    if a >/ b
       then result
       else iter (next a) (result +/ term a)
  in
    iter a (ni 0)

(* C.2.1 *)
let rec product_rec term a next b = 
  if a >/ b 
    then (ni 1)
    else term a */ (product_rec term (next a) next b) 

let factorial_rec n = 
  product_rec (fun x -> x) (ni 1) (fun x -> x +/ (ni 1)) n

let pi_product n = 
  let next m = m +/ (ni 1) in
  let num m = if mod_num m (ni 2) = (ni 0) then m +/ (ni 2) else m +/ (ni 1) in
  let den m = if mod_num m (ni 2) = (ni 0) then m +/ (ni 1) else m +/ (ni 2) in
  let top = product_rec num (ni 1) next n in
  let bottom = product_rec den (ni 1) next n in 
    (ni 4) */ top // bottom

let pi_approx = float_of_num (pi_product (ni 1000))

(* C.2.2 *)
let product_iter term a next b = 
  let rec iter a result = 
    if a >/ b 
      then result
      else iter (next a) (result */ term a)
  in
    iter a (ni 1)  

let factorial_iter n = 
  product_iter (fun x -> x) (ni 1) (fun x -> x +/ (ni 1)) n

(* C.3.1 *)
let rec accumulate_rec combiner null_value term a next b = 
  if a >/ b 
    then null_value
    else combiner (term a) (accumulate_rec combiner null_value term (next a) next b)

(* C.3.2 *)
let accumulate_iter combiner null_value term a next b = 
  let rec iter a result =
    if a >/ b 
      then result 
      else iter (next a) (combiner result (term a))
  in 
    iter a null_value

let sum term a next b =
  accumulate_rec ( +/ ) (ni 0) term a next b

let product term a next b =
  accumulate_rec ( */ ) (ni 1) term a next b

(* C.4 *)
let compose f g = 
  fun x -> f (g x)

(* C.5 *)
let rec repeated f n =
  if n = 0
    then (fun x -> x) 
    else compose f (repeated f (n - 1)) 

(* C.6 *)
let smooth dx f =
  fun x -> (f (x -. dx) +. f (x) +. f (x +. dx)) /. 3.0

let nsmoothed dx f n =
  (repeated (smooth dx) n) f

(***** PART D: ADDITIONAL PROBLEMS *****)

(* D.1 *)
let is_prime n =
  if n < 2
    then false
    else 
      let rec iter i = 
        match i with
          | i' when i' > int_of_float (sqrt (float_of_int n)) -> true
          | i' when n mod i = 0 -> false
          | _ -> iter (i + 1)
      in 
        iter 2

(* D.2 *)
let smallest_prime_factor n = 
  let rec iter i = 
    match i with
      | i' when is_prime i' && n mod i' = 0 -> i'
      | _ -> iter (i + 1)
  in 
    match n with
      | n' when is_prime n' -> invalid_arg "Input cannot be a prime number"
      | n' when n' < 2 -> invalid_arg "Input cannot be less than 2"
      | _ -> iter 2