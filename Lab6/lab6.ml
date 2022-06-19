(* PART A: THE ENVIRONMENT MODEL *)

(* A.1 *)

(*
FRAME 0 (initial environment)
  parent: none
  bindings:
    - : [primitive function -]
    * : [primitive function *]

FUNCTION 0 (fun n -> let rec iter m r = ...)
  env: FRAME 0
  param: n
  body: let rec iter m r = ...

FRAME 1 (let factorial = FUNCTION 0 in ...)
  parent: FRAME 0
  bindings:
    factorial: FUNCTION 0

FRAME 2 (FUNCTION 0 applied to 3)
  parent: FRAME 1
  bindings:
    n : 3
  
FUNCTION 1 (fun m r -> if m = 0 ...)
  env: FRAME 3
  param: m r
  body: if m = 0 ...

FRAME 3 (let rec iter m r = if m = 0 ...)
  parent: FRAME 2
  bindings:
    iter: FUNCTION 1

FRAME 4 (FUNCTION 1 applied to 3, 1)
  parent: FRAME 3
  bindings:
    m : 3
    r : 1

FRAME 5 (FUNCTION 1 applied to 2, 3)
  parent: FRAME 3
  bindings:
    m : 2
    r : 3

FRAME 6 (FUNCTION 1 applied to 1, 6)
  parent: FRAME 3
  bindings:
    m: 1
    r: 6

FRAME 7 (FUNCTION 1 applied to 0, 6)
  parent: FRAME 3
  bindings:
    m : 0
    r : 6
*)

(* A.2 *)
let factorial =
  let f = ref (fun n -> 0) in
  let helper n = 
    if n = 0
      then 1
      else n * !f (n - 1) in
  begin
    f := helper;
  end;
  !f 

(* PART B: OBJECTS AND MUTATION *)

(* B.1 *)
exception Stat_error of string

let make_stat_1 () =
  let sum = ref 0.0 in
  let sumsq = ref 0.0 in
  let n = ref 0 in
    object
      method append x = 
        begin
          sum := !sum +. x;
          sumsq := !sumsq +. x *. x;
          n := !n + 1
        end
      method mean =
        begin
          if !n = 0 then raise (Stat_error "need at least one value for mean")
          else !sum /. (float_of_int !n)
        end
      method stdev =
        begin
          if !n = 0 then raise (Stat_error "need at least one value for stdev")
          else 
            sqrt ((!sumsq -. !sum *. !sum /. (float_of_int !n)) /. 
              (float_of_int !n))
        end
      method variance = 
        begin
          if !n = 0 
            then 
              raise (Stat_error "need at least one value for variance")
            else 
              (!sumsq -. !sum *. !sum /. (float_of_int !n)) /. (float_of_int !n)
        end
      method clear = 
        begin
          sum := 0.0;
          sumsq := 0.0;
          n := 0
        end
    end

(* B.2 *)
let make_stat_2 () = 
  let sum = ref 0.0 in
  let sumsq = ref 0.0 in
  let n = ref 0 in
    object (self)
      method append x = 
        begin
          sum := !sum +. x;
          sumsq := !sumsq +. x *. x;
          n := !n + 1
        end
      method mean =
        begin
          if !n = 0 then raise (Stat_error "need at least one value for mean")
          else !sum /. (float_of_int !n)
        end
      method private _variance = 
        (!sumsq -. !sum *. !sum /. (float_of_int !n)) /. (float_of_int !n)
      method stdev =
        begin
          if !n = 0 then raise (Stat_error "need at least one value for stdev")
          else 
            sqrt (self#_variance)
        end
      method variance = 
        begin
          if !n = 0 
            then 
              raise (Stat_error "need at least one value for variance")
            else 
              self#_variance
        end
      method clear = 
        begin
          sum := 0.0;
          sumsq := 0.0;
          n := 0
        end
    end

(* PART C: MODULES AND FUNCTORS *)

(* C.1 *)
module type PRIORITY_QUEUE =
  sig
    exception Empty

    type elem      (* Abstract type of elements of queue. *)
    type t         (* Abstract type of queue. *)

    val empty      : t                (* The empty queue.         *)
    val is_empty   : t -> bool        (* Check if queue is empty. *)
    val insert     : t -> elem -> t   (* Insert item into queue.  *)
    val find_min   : t -> elem        (* Return minimum element.  *)
    val delete_min : t -> t           (* Delete minimum element.  *)
    val from_list  : elem list -> t   (* Convert list to queue.   *)
  end

module PriorityQueue : (PRIORITY_QUEUE with type elem = int) =
  struct
    exception Empty
    type elem = int
    type t = Leaf | Node of int * elem * t * t

    let empty = Leaf
    let is_empty t = (t = Leaf)

    let rank n = 
      match n with
        | Leaf -> 0
        | Node (r, _, _, _) -> r 

    let rec merge q1 q2 =
      let helper q1' q2' min_elem =
        let rank1' = rank q1' in 
        let rank2' = rank q2' in
          if rank2' > rank1'
            then Node (rank1' + 1, min_elem, q2', q1')
            else Node (rank2' + 1, min_elem, q1', q2')
      in
        match (q1, q2) with 
          | (Leaf, _) -> q2
          | (_, Leaf) -> q1
          | (Node (rank1, elem1, l1, r1), Node (rank2, elem2, l2, r2)) ->
              if elem1 < elem2 
                then helper l1 (merge r1 q2) elem1
                else helper l2 (merge r2 q1) elem2
    
    let insert q new_elem =
      merge q (Node (1, new_elem, Leaf, Leaf))
    let find_min q = 
      match q with
        | Leaf -> raise Empty
        | Node (rank, elem, l, r) -> elem
    let delete_min q = 
      match q with 
        | Leaf -> raise Empty
        | Node (rank, elem, l, r) -> merge l r
    let rec from_list lst = 
      match lst with
        | [] -> Leaf
        | h :: t -> insert (from_list t) h
  end

let heap_sort lst =
  let rec iter result q = 
    if PriorityQueue.is_empty q 
      then List.rev result
      else 
        let min = PriorityQueue.find_min q in
        let q' = PriorityQueue.delete_min q in
          iter (min :: result) (q')
    in
      iter [] (PriorityQueue.from_list lst)

(* C.2 *)
(* Type for ordered comparisons. *)
type comparison = LT | EQ | GT

(* Signature for ordered objects. *)
module type ORDERED =
  sig
    type t
    val cmp: t -> t -> comparison
  end

module MakePriorityQueue (Elt : ORDERED)
  : (PRIORITY_QUEUE with type elem = Elt.t) =
  struct
    exception Empty
    type elem = Elt.t
    type t = Leaf | Node of int * elem * t * t

    let empty = Leaf
    let is_empty t = (t = Leaf)

    let rank n = 
      match n with
        | Leaf -> 0
        | Node (r, _, _, _) -> r 

    let rec merge q1 q2 =
      let helper q1' q2' min_elem =
        let rank1' = rank q1' in 
        let rank2' = rank q2' in
          if rank2' > rank1'
            then Node (rank1' + 1, min_elem, q2', q1')
            else Node (rank2' + 1, min_elem, q1', q2')
      in
        match (q1, q2) with 
          | (Leaf, _) -> q2
          | (_, Leaf) -> q1
          | (Node (rank1, elem1, l1, r1), Node (rank2, elem2, l2, r2)) ->
              if elem1 < elem2 
                then helper l1 (merge r1 q2) elem1
                else helper l2 (merge r2 q1) elem2
    
    let insert q new_elem =
      merge q (Node (1, new_elem, Leaf, Leaf))
    let find_min q = 
      match q with
        | Leaf -> raise Empty
        | Node (rank, elem, l, r) -> elem
    let delete_min q = 
      match q with 
        | Leaf -> raise Empty
        | Node (rank, elem, l, r) -> merge l r
    let rec from_list lst = 
      match lst with
        | [] -> Leaf
        | h :: t -> insert (from_list t) h
  end

module OrderedString =
  struct
    type t = string
    let cmp x y =
      if x = y then EQ else if x < y then LT else GT
  end

module StringPQ = MakePriorityQueue(OrderedString)

let heap_sort_2 lst =
  let rec iter result q = 
    if StringPQ.is_empty q 
      then List.rev result
      else 
        let min = StringPQ.find_min q in
        let q' = StringPQ.delete_min q in
          iter (min :: result) (q')
    in
      iter [] (StringPQ.from_list lst)

(* PART D: SPECIAL TOPICS *)

(* D.1 *)
type 'a contents = Eval of 'a | Uneval of (unit -> 'a)
type 'a lazy_t = 'a contents ref

let make_lazy e = ref (Uneval e)
let force lz = 
  match !lz with 
    | Eval v -> v
    | Uneval expr ->
        begin
          lz := Eval (expr ());
          expr ()
        end
        

(* D.2 *)
let y =
  fun f ->
    (fun z -> z (`Roll z))
    (fun (`Roll w) -> f (fun x -> w (`Roll w) x))

(* D.2.a *)
let almost_sum =
  fun f -> 
    fun lst ->
      match lst with
        | [] -> 0
        | h :: t -> h + (f t)

let sum = y almost_sum

(* D.2.b *)
let factorial2 n = 
  let iter = 
    fun f ->
      fun (n, result) -> 
        if n = 0
          then result
          else f (n - 1, n * result)
  in y iter (n, 1)
