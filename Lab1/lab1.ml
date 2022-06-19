(* A.1 *)
(*
1) 
  - : int = 10
2) 
  - : float = 10.
3) 
  - : int = 12
4) 
  Error: This expression has type float but an expression was expected of type 
         int
  -This error occurred because we need +. for addition between floats since + 
  is for addition between integers.
5) 
  Error: This expression has type int but an expression was expected of type
         float
  Hint: Did you mean `3.'?
  -This error occurred because +. is for float addition but 3 and 4 are 
  integers, so integer addition with + should have been used.
6) 
  Error: This expression has type float but an expression was expected of type
         int
  -This error occurred because integer addition was attempted between an integer
  and a float.

7) 
  Error: This expression has type int but an expression was expected of type
         float
  Hint: Did you mean `3.'?
  -This error occured because float addition was attempted between an integer
  and a float.
8) 
  - : float = 7.2
9) 
  - : int = 5
10) 
  - : int = 7
11) 
  val a : int = 3
12) 
  val b : int = 4
13) 
  - : bool = false
14) 
  - : bool = true
15) 
  - : bool = false
  -This is different from the previous expression because "==" checks if the two
  arguments are identical in memory.
16) 
  - : (int * int * int) list = [(1, 2, 3)]
17) 
  - : (int * int * int) list = [(1, 2, 3)]
  -This result is given because commas were used to separate the values, so it
  is returned as a single element 3-tuple rather than a list.  Semicolons need 
  to be used as separators for lists.
18) 
  - : int = 4
19) 
  Error: Syntax error
  -This error occurred because the valid AND operator for OCaml is "&&" rather 
  than "and".
20) 
  - : int = 6
21) 
  - : int = 4
  -This is different than the previous case because the + 2 is only associated
  with the else case in this situation.
22) 
  - : int = 6
23) 
  Error: This expression has type int but an expression was expected of type
         unit
       because it is in the result of a conditional with no else branch
  -This error occurred because the return type must be unit if there is not else
  clause.  The type is assumed to be unit in this situation.
*)

(* A.2 *)
let sum_of_squares_of_two_largest a b c =
  if a > c && b > c then a * a + b * b 
  else if a > b then a * a + c * c
  else b * b + c * c

(* A.3 *)
(*
  This function returns the equivalent of a + |b| (a plus absolute value of b).
*)

(* B.1 *)
(*
  With an intepreter that uses applicative order evaluation, Ben will observe 
  infinite recursion because the arguments 0 and p () will be evaluated first, 
  and p () will recurse forever.  With normal order evaluation, p () won't be 
  evaluated because 0 will be returned since the condition 0 = 0 is checked 
  first.
*)

(* B.2 *)
(*
  Alyssa will encounter an infinite loop since new_if is a function, so in 
  sqrt_iter, the arguments to new_if will be evaluated first.  Thus, with one of
  the arguments being (sqrt_iter (improve guess x) x), the sqrt_iter in this 
  argument will call new_if again where this loop will continue without 
  stopping.
*)

(* B.3 *)
(*
1) 
  The function add_a generates recursive processes while add_b generates 
  iterative processes.  This is because add_a adds something with inc to the 
  result of the recursive call, while add_b just has the recursive call.

2)
  Evaluate: add_a 2 5
    evaluate 2 -> 2
    evaluate 5 -> 5
    evaluate add_a ->
      fun a b -> ...
    apply fun a b -> ... to 2, 5
      substitute 2 for a, 5 for b in ...
        -> if 2 = 0 then 5 else inc (add_a (dec 2) 5)
      evaluate if 2 = 0 then 5 else inc (add_a (dec 2) 5) [special form]
      *if is a special form, so evaluate the first operand
        evaluate 2 = 0 
          evaluate 2 -> 2
          evaluate 0 -> 0
          evaluate = -> =
          apply = to 2 and 0 -> false
        evaluate inc (add_a (dec 2) 5) [special form]
        *first argument of if is false, so evaluate the third operand
          evaluate add_a (dec 2) 5)
            evaluate dec 2
              evaluate 2 -> 2
              evaluate dec -> dec
              apply dec to 2 -> 1
            evaluate 5 -> 5
            evaluate add_a ->
              fun a b -> ...
            apply fun a b -> ... to 1, 5
              substitute 1 for a, 5 for b in ...
                -> if 1 = 0 then 5 else inc (add_a (dec 2) 5)
              evaluate if 1 = 0 then 5 else inc (add_a (dec 1) 5) [special form]
              *if is a special form, so evaluate the first operand
                evaluate 1 = 0
                  evaluate 1 -> 1
                  evaluate 0 -> 0
                  evaluate = -> =
                  apply = to 1 and 0 -> false
                evaluate inc (add_a (dec 1) 5) [special form]
                *first argument of if is false, so evaluate the third operand
                  evaluate add_a (dec 1) 5
                    evaluate dec 1
                      evaluate 1 -> 1
                      evaluate dec -> dec
                      apply dec to 1 -> 0
                    evaluate 5 -> 5
                    evaluate add_a ->
                      fun a b -> ...
                    apply fun a b -> ... to 0, 5
                      substitute 0 for a, 5 for b in ...
                        -> if 0 = 0 then 5 else inc (add_a (dec 2) 5)
                      evaluate if 0 = 0 then 5 else inc (add_a (dec 2) 5) [special form]
                      *if is a special form, so evaluate the first operand
                        evaluate 0 = 0
                          evaluate 0 -> 0
                          evaluate 0 -> 0
                          evaluate = -> =
                          apply = to 0 and 0 -> true
                        evaluate 5 -> 5 [special form]
                        *first argument of if is true, so evaluate second operand
                evaluate inc -> inc
                apply inc to 5 -> 6
        evaluate inc -> inc
        apply inc to 6 -> 7
    result: 7

3)
  let rec add_b a b =
    if a = 0
      then b
      else add_b (dec a) (inc b)

  Desugar this to:

  let rec add_b =
    fun a b ->
      if a = 0
        then b
        else add_b (dec a) (inc b)

  Bind the name "add_b" to the value:

    fun a b ->
      if a = 0
        then b
        else add_b (dec a) (inc b)

  Evaluate (add_b 2 5)
    >>> evaluate 2 -> 2
    >>> evaluate 5 -> 5
    >>> evaluate add_b ->
      >>> fun a b -> ...
    apply (fun a b -> if ...) to 2, 5
    substitute 2 for a, 5 for b in (if ...)
      -> if 2 = 0 then 5 else add_b (dec 2) (inc 5)
    evaluate (if 2 = 0 then 5 else add_b (dec 2) (inc 5))
      if is a special form, so evaluate the first operand:
        evaluate (2 = 0)
          >>> evaluate 2 -> 2
          >>> evaluate 0 -> 0
          >>> evaluate = -> =
          apply = to 2, 0 -> false
      first argument of if is false, so evaluate the third operand:
        evaluate (add_b (dec 2) (inc 5))
          evaluate (dec 2)
            >>> evaluate 2 -> 2
            >>> evaluate dec -> dec
            apply dec to 2 -> 1
          evaluate (inc 5)
            >>> evaluate 5 -> 5
            >>> evaluate inc -> inc
            apply inc to 5 -> 6
          apply (fun a b -> if ...) to 1, 6
          substitute 1 for a, 6 for b in (if ...)
            -> if 1 = 0 then 6 else add_b (dec 1) (inc 6)
          evaluate (if 1 = 0 then 6 else add_b (dec 1) (inc 6))
            if is a special form, so evaluate the first operand:
              evaluate (1 = 0)
                >>> evaluate 1 -> 1
                >>> evaluate 0 -> 0
                >>> evaluate = -> =
                apply = to 1, 0 -> false
            first argument of if is false, so evaluate the third operand:
              evaluate (add_b (dec 1) (inc 6))
                evaluate (dec 1)
                  >>> evaluate 1 -> 1
                  >>> evaluate dec -> dec
                  apply dec to 1 -> 0
                evaluate (inc 6)
                  >>> evaluate 6 -> 6
                  >>> evaluate inc -> inc
                  apply inc to 6 -> 7
                apply (fun a b -> if ...) to 0, 7
                substitute 0 for a, 7 for b in (if ...)
                  -> if 0 = 0 then 7 else add_b (dec 0) (inc 7)
                evaluate (if 0 = 0 then 7 else add_b (dec 0) (inc 7))
                  if is a special form, so evaluate the first operand:
                    evaluate (0 = 0)
                    >>> evaluate 0 -> 0
                    >>> evaluate 0 -> 0
                    >>> evaluate = -> =
                      apply = to 0, 0 -> true
                  first argument of if is true, so evaluate the second operand:
                    result: 7
*)

(* C.1 *)
let rec factorial n =
  if n = 0 then 
    1 
  else n * factorial (n - 1)

(* a *)
let e_term n = 
  1. /. float_of_int (factorial n)

(* b *)
let rec e_approximation n = 
  if n < 0 then
    invalid_arg "input must be non-negative"
  else
    if n = 0 then 
      e_term n 
    else
      e_term n +. e_approximation (n - 1)

(* c *)
(*
  e_approximation 20 = 2.71828182845904553
  exp 1.0 = 2.71828182845904509
  -The results are extremely similar.
*)

(* d *)
(*
  The result is infinity which occurs because OCaml is unable to achieve the 
  same precision for n! in the 1/n! term for e_term n.
*)

(* C.2 *)
let rec is_even n =
  if n = 0 then
    true
  else
    is_odd (n - 1)
and is_odd n =
  if n = 0 then
    false
  else
    is_even (n - 1)

(* C.3 *)
let rec f_rec n =
  if n < 3 then
    n
  else
    f_rec (n - 1) + 2 * f_rec (n - 2) + 3 * f_rec (n - 3)

let rec f_iter_helper n d f x y =
  if n < d then 
    f
  else
    f_iter_helper n (d + 1) (f + 2 * x + 3 * y) f x
  
let f_iter n = 
  if n < 3 then
    n 
  else
    f_iter_helper n 3 2 1 0

(* C.4 *)
let rec pascal_coefficient row_num index =
  match row_num, index with
    | row_num', index' when index' > row_num' -> failwith "invalid arguments"
    | row_num', _ when row_num' < 1 -> failwith "invalid arguments"
    | _, index' when index' < 1 -> failwith "invalid arguments"
    | row_num', index' when row_num' = index' -> 1
    | _, 1 -> 1
    | _, _ -> pascal_coefficient (row_num - 1) (index - 1) + pascal_coefficient (row_num - 1) (index)