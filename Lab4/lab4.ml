(****** PART A: ABSTRACTION ******)

(* A.1 *)
type point = { x : float ; y : float}
type segment = { startp : point ; endp : point}

let midpoint_segment { startp; endp } =
  let x = (startp.x +. endp.x) /. 2.0 in
  let y = (startp.y +. endp.y) /. 2.0 in
    { x ; y } 

let segment_length { startp; endp } = 
  let a = abs_float (endp.x -. startp.x) in
  let b = abs_float (endp.y -. startp.y) in
    sqrt (a *. a +. b *. b)

let print_point { x; y } = 
  Printf.printf "(%g, %g)\n" x y

let make_point x y =
  { x = x ; y = y }

let get_coords { x; y} =
  (x, y)

let make_segment startp endp = 
  { startp = startp ; endp = endp}

let get_points { startp; endp } =
  (startp, endp)

(* A.2 *)
type rectangle = { 
  ll : point ; 
  ur : point 
  }

let rectangle_lower_segment { ll; ur } =
  make_segment ll (make_point ur.x ll.y)

let rectangle_upper_segment { ll; ur } =
  make_segment (make_point ll.x ur.y) ur

let rectangle_left_segment { ll; ur } =
  make_segment ll (make_point ll.x ur.y)

let rectangle_right_segment { ll; ur } =
  make_segment (make_point ur.x ll.y) ur

let rectangle_perimeter rect = 
  let lower_length = segment_length (rectangle_lower_segment rect) in
  let left_length = segment_length (rectangle_left_segment rect) in
    2.0 *. (lower_length +. left_length)

let rectangle_area rect = 
  let lower_length = segment_length (rectangle_lower_segment rect) in
  let left_length = segment_length (rectangle_left_segment rect) in
    lower_length *. left_length

let make_rectangle ll ur = 
  { ll = ll ; ur = ur }

type rectangle2 = {  
  lx : float ; 
  ly : float ;
  ux : float ;  
  uy : float 
  }

let rectangle_lower_segment2 { lx; ly; ux; uy } =
  make_segment (make_point lx ly) (make_point ux ly)

let rectangle_upper_segment2 { lx; ly; ux; uy } =
  make_segment (make_point lx uy) (make_point ux uy)

let rectangle_left_segment2 { lx; ly; ux; uy } =
  make_segment (make_point lx ly) (make_point lx uy)

let rectangle_right_segment2 { lx; ly; ux; uy } =
  make_segment (make_point ux uy) (make_point ux ly)

let rectangle_perimeter2 rect =
  let lower_length = segment_length (rectangle_lower_segment2 rect) in
  let left_length = segment_length (rectangle_left_segment2 rect) in
    2.0 *. (lower_length +. left_length)

let rectangle_area2 rect = 
  let lower_length = segment_length (rectangle_lower_segment2 rect) in
  let left_length = segment_length (rectangle_left_segment2 rect) in
    lower_length *. left_length

let make_rectangle2 lx ly ux uy = 
  { lx = lx ; ly = ly ; ux = ux ; uy = uy }

(* A.3 *)
let make_pair x y = fun m -> m x y
let first z = z (fun x y -> x)
let second z = z (fun x y -> y)

(*
  We see that first takes in (fun m -> m x y) as its argument z, where the 
  argument m becomes (fun x y -> x).  Thus, with x and y as its arguments, x is
  yielded as the result of first (make_pair x y) for any objects x and y.
*)

(*
  Evaluate second (make_pair 1 2):
    evaluate make_pair 1 2
      evaluate 1 -> 1
      evaluate 2 -> 2
      evaluate make_pair -> ...
        fun x y -> ... fun m -> m x y
      apply fun x y -> ... to 1, 2
        substitute 1 for x, 2 for y in ...
          fun m -> m 1 2
    evaluate second -> 
      fun z -> z (fun x y -> y)
    apply fun z -> ... to (fun m -> m 1 2)
      substitute (fun m -> m 1 2) for z in ...
        (fun m -> m 1 2) (fun x y -> y)
      evaluate (fun m -> m 1 2) (fun x y -> y)
      evaluate (fun m -> 1 2) -> (fun m -> 1 2)
      evaluate (fun x y -> y) -> (fun x y -> y)
      apply (fun m -> 1 2) -> (fun x y -> y)
        substitute (fun x y -> y) for m in ...
          (fun x y -> y) 1 2
        evaluate (fun x y -> y) 1 2
        evaluate 1 -> 1
        evaluate 2 -> 2
        evaluate (fun x y -> y) -> (fun x y -> y)
        apply (fun x y -> y) to 1, 2
        substitute 1 for x, 2 for y in ...
          2
  Result: 2
*)

(* A.4 *)
let rec pow a b =
  if b = 0 then 1
  else a * pow a (b - 1)

let int_log base i  =
  let rec iter base i count = 
    match i with
      | i when i mod base = 0 -> iter base (i / base) (count + 1)
      | _ -> count
  in 
    iter base i 0

let make_pairi a b = 
  (pow 2 a) * (pow 3 b)

let firsti pair =
  int_log 2 pair

let secondi pair = 
  int_log 3 pair

(* A.5 *)
let zero = []

let is_zero = function
  | [] -> true
  | () :: _ -> false

let succ u = () :: u

let prev = function 
  | [] -> invalid_arg "Argument must be greater than (unary) zero"
  | () :: t -> t

let rec integer_to_unary i = 
  if i = 0 then
    zero
  else 
    succ (integer_to_unary (i - 1))

let rec unary_to_integer u =
  if is_zero u then
    0
  else
    1 + unary_to_integer (prev u)

let unary_add u1 u2 =
  integer_to_unary ((unary_to_integer u1) + (unary_to_integer u2))

type nat = Zero | Succ of nat

let zero' = Zero

let is_zero' = function
  | Zero -> true
  | Succ _ -> false

let succ' u = Succ u

let prev' = function
  | Zero -> invalid_arg "Argument must be greater than (unary) zero"
  | Succ t -> t

(* 
  The other definitions (integer_to_unary, unary_to_integer, unary_add) do not
  have to change (besides name obvious name changes).
*)

let rec integer_to_unary' i = 
  if i = 0 then
    zero'
  else 
    succ' (integer_to_unary' (i - 1))

let rec unary_to_integer' u =
  if is_zero' u then
    0
  else
    1 + unary_to_integer' (prev' u)

let unary_add' u1 u2 =
  integer_to_unary' ((unary_to_integer' u1) + (unary_to_integer' u2))

(* A.6 *)
(* zerof = "functional zero"; we call it this so as not to be confused with
   zero or zero' previously defined. *)

let zerof = fun s -> fun z -> z
(* or equivalently: let zerof = fun s z -> z *)
(* or equivalently: let zerof s z = z *)
 
let add1 n = fun s -> fun z -> s (n s z)
  (* or equivalently: let add1 n = fun s z -> s (n s z) *)
  (* or equivalently: let add1 n s z = s (n s z) *)

let one = fun s -> fun z -> s z
let two = fun s -> fun z -> s (s z)
let three = fun s -> fun z -> s (s (s z))
let four = fun s -> fun z -> s (s (s (s z)))
let five = fun s -> fun z -> s (s (s (s (s z))))
let six = fun s -> fun z -> s (s (s (s (s (s z)))))
let seven = fun s -> fun z -> s (s (s (s (s (s (s z))))))
let eight = fun s -> fun z -> s (s (s (s (s (s (s (s z)))))))
let nine = fun s -> fun z -> s (s (s (s (s (s (s (s (s z))))))))
let ten = fun s -> fun z -> s (s (s (s (s (s (s (s (s (s z)))))))))

let add m n s z = m s (n s z)

let church_to_integer n = n (fun x -> x + 1) 0

(* A.7 *)
(*
  Let us first establish:
    val church_to_integer : ((int -> int) -> (int -> 'c)) -> 'c = <fun>
    val zerof : 'a -> ('b -> 'b) = <fun>
    val one : ('a -> 'b) -> ('a -> 'b) = <fun>

  With church_to_integer zerof, we see that the type of 'a corresponds to (int 
  -> int), the type of 'b corresponds to int, and the type of (int -> 'c) 
  corresponds to ('b -> 'b).  So, the type of 'c must be int.

  With church_to_integer one, we see that the type of 'a corresponds to int, the
  type of 'b corresponds to int, and the type of (int -> 'c) corrresponds to 
  ('a -> 'b).  So, the type of 'c must b int also.
*)

(****** PART B: MORE ABSTRACTION PROBLEMS ******)

(* B.1 *)
type mobile = Mobile of branch * branch  (* left and right branches *)
and branch =
  | Weight    of int * int     (* length and weight *)
  | Structure of int * mobile  (* length and sub-mobile *)

let make_mobile l r = Mobile (l, r)
let make_weight l w = Weight (l, w)
let make_structure l m = Structure (l, m)

(* B.1.a *)
let left_branch = function
  | Mobile (l, r) -> l

let right_branch = function 
  | Mobile (l, r) -> r

let branch_length = function
  | Weight (l, w) -> l
  | Structure (l, m) -> l

let branch_structure = function
  | Weight (l, w) -> `Weight w
  | Structure (l, m) -> `Structure m

(* B.1.b *)
let rec branch_weight1 = function
  | Weight (l, w) -> w
  | Structure (l, m) -> total_weight1 m
and total_weight1 = function 
  | Mobile (l, r) -> (branch_weight1 l) + (branch_weight1 r)

let rec branch_weight2 branch =
  match branch_structure branch with
    | `Weight w -> w
    | `Structure m -> total_weight2 m
and total_weight2 m = 
  (branch_weight2 (left_branch m)) + (branch_weight2 (right_branch m))

(* B.1.c *)
let rec is_balanced mobile =
  let is_branch_balanced branch = 
    match branch_structure branch with 
      | `Weight w -> true
      | `Structure m -> is_balanced m
  in
  let left = left_branch mobile in
  let right = right_branch mobile in
    if (branch_weight2 left) * (branch_length left) == 
      (branch_weight2 right) * (branch_length right) then
        (is_branch_balanced left) && (is_branch_balanced right)
    else
      false

(* B.1.d *)
type mobile' = { left: branch'; right: branch' }
and branch' = Branch' of int * contents
and contents = Weight' of int | Structure' of mobile'

let make_mobile' left right = { left = left ; right = right }
let make_weight' l w = Branch' (l, (Weight' w))
let make_structure' l m = Branch' (l, (Structure' m))
let left_branch' { left; right } = left
let right_branch' { left; right } = right
let branch_length' (Branch' (l, m)) = l
let branch_structure' (Branch' (l, m)) = 
      match m with 
        | Weight' w -> `Weight w
        | Structure' s -> `Structure s

let rec branch_weight' branch =
  match branch_structure' branch with
    | `Weight w -> w
    | `Structure m -> total_weight' m
and total_weight' m = 
  (branch_weight' (left_branch' m)) + (branch_weight' (right_branch' m))

let rec is_balanced' mobile =
  let is_branch_balanced branch = 
    match branch_structure' branch with 
      | `Weight w -> true
      | `Structure m -> is_balanced' m
  in
  let left = left_branch' mobile in
  let right = right_branch' mobile in
    if (branch_weight' left) * (branch_length' left) == 
      (branch_weight' right) * (branch_length' right) then
        (is_branch_balanced left) && (is_branch_balanced right)
  else
    false

(* B.2 *)
type tree = Tree of elem list
and elem =
  | Num of int
  | Sub of tree

let rec square_tree (Tree t) = 
  let rec square = function
    | [] -> []
    | (Num h) :: t -> (Num (h * h)) :: (square t)
    | (Sub h) :: t -> (Sub (square_tree h)) :: (square t)
in 
  Tree (square t)

let rec square_tree' (Tree t) =
  let square = function 
    | Num n -> Num (n * n)
    | Sub s -> Sub (square_tree' s)
  in Tree (List.map square t)

(* B.3 *)
let rec tree_map f (Tree t) =
  let f' = function 
    | Num n -> Num (f n)
    | Sub s -> Sub (tree_map f s)
  in Tree (List.map f' t)

(****** PART C: MINIPROJECT: ALGEBRAIC EXPRESSIONS ******)

type expr =
  | Int of int           (* constant *)
  | Var of string        (* variable *)
  | Add of expr * expr   (* expr1 + expr2 *)
  | Mul of expr * expr   (* expr1 * expr2 *)
  | Pow of expr * int    (* expr^n *)

(* C.1 *)
let rec simplify1 = function 
  | Int a -> Int a
  | Var a -> Var a
  | Add (Int a, Int b) -> Int (a + b)
  | Add (expr1, Int 0) | Add (Int 0, expr1) -> expr1
  | Add (expr1, expr2) -> Add (simplify expr1, simplify expr2)
  | Mul (Int a, Int b) -> Int (a * b)
  | Mul (expr1, Int 0) | Mul (Int 0, expr1) -> Int 0
  | Mul (expr1, Int 1) | Mul (Int 1, expr1) -> expr1
  | Mul (expr1, expr2) -> Mul (simplify expr1, simplify expr2)
  | Pow (expr1, 0) -> Int 1
  | Pow (expr1, 1) -> expr1
  | Pow (Int a, b) -> Int (pow a b)
  | Pow (expr1, a) -> Pow (simplify expr1, a)
and simplify expr =
  let e = simplify1 expr in
    if expr = e
      then expr
      else simplify e

(* C.2 *)
let rec deriv x expr = 
  match expr with 
    | Int a -> Int 0
    | Var a -> if a = x then Int 1 else Int 0
    | Add (expr1, expr2) -> Add ((deriv x expr1), (deriv x expr2))
    | Mul (expr1, expr2) -> 
        Add ((Mul (deriv x expr1, expr2)), (Mul (expr1, deriv x expr2)))
    | Pow (expr1, n) -> Mul (Mul (Int n, Pow (expr1, (n - 1))), deriv x expr1)

let derivative var expr =
  let e = simplify expr in
  let d = deriv var e in
    simplify d