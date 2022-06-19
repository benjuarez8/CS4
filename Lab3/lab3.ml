(****** PART A: WORKING WITH LISTS ******)

(* A.1 *)
let rec last_sublist = function
  | [] -> invalid_arg "last_sublist: empty list"
  | [n] -> [n]
  | h :: t -> last_sublist t 

(* A.2 *)
let reverse lst = 
  let rec iter curr reversed =
    match curr with
      | [] -> reversed
      | h :: t -> iter t (h :: reversed)
  in 
    iter lst []

(* A.3 *)
let rec square_list = function
  | [] -> []
  | h :: t -> h * h :: square_list t

let square_list2 items = List.map (fun x -> x * x) items

(* A.4 *)
(*
  Doing it this first way produces the answer list in reverse order because each
  iteration squares the head element and adds it to the front of answer where 
  the first iteration squares the first element and adds it to an empty list.
  So, this results in the first element of the original list becoming the last
  element in the result list as all of the following elements are squared and 
  added in front of the first element, thus the desired output is not achieved.

  Louis's attempt to fix this bug fails because "answer :: (h * h)" is not valid
  because the :: constructor expects a list to be the right-handed argument, and
  (h * h) is not a list.

  Modified second solution:
  let square_list items =
  let rec iter things answer =
    match things with
      | [] -> answer
      | h :: t -> iter t (answer @ [h * h])
  in iter items []

  It does not seem like this modified solution would be as efficient as expected
  because the @ operator means that at each iteration, all elements in the list
  have to be copied over.  Thus, each iteration operates in O(n) time, so the entire
  function runs in O(n^2) time which is not great for larger lists.
*)

(* A.5 *)
let rec count_negative_numbers = function
  | [] -> 0
  | h :: t ->
    if h < 0 
      then 1 + count_negative_numbers t
      else 0 + count_negative_numbers t

(* A.6 *)
let power_of_two_list n =
  let rec pow a b = 
    if b = 0
      then 1
      else a * pow a (b - 1)
  in
  let rec iter i result =
    if i < 0
      then result
      else iter (i - 1) (pow 2 i :: result)
  in 
    iter (n - 1) []

(* A.7 *)
let prefix_sum lst =
  let rec iter lst p = 
    match lst with
      | [] -> []
      | h :: t -> (h + p) :: (iter t (h + p)) 
  in 
    iter lst 0

(* A.8 *)
let deep_reverse lst = 
  let rec iter curr reversed = 
    match curr with
      | [] -> reversed
      | h :: t -> iter t ((reverse h) :: reversed)
  in 
    iter lst []

(* A.9 *)
type 'a nested_list =
  | Value of 'a
  | List of 'a nested_list list

let rec deep_reverse_nested lst = 
  let rec iter curr rev = 
    match curr with 
      | [] -> rev
      | h :: t -> iter t ((deep_reverse_nested h) :: rev)
  in 
    match lst with
      | Value a -> Value a
      | List a -> List (iter a [])


(****** PART B: STRUCTURAL AND GENERATIVE RECURSION ******)

(* B.1 *)
let rec filter predicate sequence =
  match sequence with
    | [] -> []
    | h :: t when predicate h -> h :: filter predicate t
    | _ :: t -> filter predicate t

let rec quicksort lst cmp = 
  match lst with
    | [] -> []
    | h :: t ->
      let lst1 = filter (fun x -> cmp x h) t in
      let lst2 = filter (fun x -> not (cmp x h)) t in
        (quicksort lst1 cmp) @ (h :: quicksort lst2 cmp)

(* B.2 *)
(*
  The quicksort function is an instance of generative recursion because the 
  sublists that are quicksorted on are not "natural" subparts of data.  Rather, 
  this function recurses on subparts of the data that "we" generate which is 
  this case is dependent on the pivot.
*)

(* B.3 *)
(*
  This won't work, specifically in the case of the a_list argument being a list
  of length one.  This is because an infinite loop will occur when "merge_sort 
  oh cmp" where oh is a copy of the 1-element list.  This problem does not occur
  if lists of length 1 are checked properly.
*)

(* B.4 *)
let rec insert_in_order new_result a_list cmp =
  match a_list with
    | [] -> [new_result]
    | h :: t when cmp new_result h -> new_result :: a_list
    | h :: t ->  h :: insert_in_order new_result t cmp

let rec insertion_sort a_list cmp =
  match a_list with
    | [] -> []
    | h :: t -> insert_in_order h (insertion_sort t cmp) cmp

(*
  This is an example of structural recursion because there is recursion on 
  "natural" subparts of the data in the sense that it starts with the head 
  (first element) and then uses the tail (rest of the list).
*)


(****** PART C: SOME HARDER PROBLEMS WITH LISTS ******)

(* C.1 *)
let rec subsets = function
  | [] -> [[]]
  | h :: t -> let rest = subsets t in
      rest @ (List.map (fun x -> h :: x) rest)

(*
  This function works by recursively removing the head of the list and "solves" 
  for all of the possible subsets for the new list without the head.  The heads
  of the lists are then added to each sublist produced by this recursion along 
  with the original sublists being appended as well with the @ operator.  In 
  other words, the function continues to remove the head and recurse on the 
  tail sublist until the empty case is reached.  Accounting for the sublists 
  with and without the head element allows for all possible subsets to be 
  accounted for.
*)

(* C.2 *)
let rec accumulate op initial sequence =
  match sequence with
    | [] -> initial
    | h :: t -> op h (accumulate op initial t)

let map p sequence =
  accumulate (fun x r -> (p x) :: r) [] sequence

let append seq1 seq2 =
  accumulate (fun x r -> x :: r) seq2 seq1

let length sequence =
  accumulate (fun x r -> 1 + r) 0 sequence

(* C.3 *)
let rec accumulate_n op init seqs =
  match seqs with
    | [] -> failwith "empty list"
    | [] :: _ -> []   (* assume all sequences are empty *)
    | h :: t -> accumulate op init (map List.hd seqs) :: 
    accumulate_n op init (map List.tl seqs)

(* C.4 *)
let rec map2 f x y =
  match (x, y) with
    | ([], []) -> []
    | ([], _) -> failwith "unequal lists"
    | (_, []) -> failwith "unequal lists"
    | (h :: t, h' :: t') -> (f h h') :: (map2 f t t') 

let dot_product v w = accumulate (+) 0 (map2 ( * ) v w)

let matrix_times_vector m v = map (fun x -> (dot_product v x)) m

let transpose mat = accumulate_n (fun x r -> x :: r) [] mat

let matrix_times_matrix m n =
  let cols = transpose n in
     map (fun x -> matrix_times_vector cols x)  m