(* name: Benjamin Juarez *)
(* email: bjuarez@caltech.edu *)

(* A.1 *)
let list_of_string s =
  let rec iter i =
    if i = (String.length s) 
      then []
      else s.[i] :: iter (i + 1) 
    in  
      iter 0

(* A.2 *)

let rec remove_exact_matches l1 l2 =
  match (l1, l2) with
    | ([], []) -> ([], [])
    | ([], _) -> failwith "remove_exact_matches: lists of different lengths"
    | (_, []) -> failwith "remove_exact_matches: lists of different lengths"
    | (h1::t1, h2::t2) -> 
        if h1 = h2 
          then let (l, r) = remove_exact_matches t1 t2 in
            ('_' :: l, '_' :: r)
          else let (l, r) = remove_exact_matches t1 t2 in
            (h1 :: l, h2 :: r)

(* 
  The worst-case asymptotic time complexity of this function is O(n).  Each 
  list input has n elements and we simulate recursively iterating through 
  each list and comparing the corresponding pairs of elements between the 
  two lists.  Note that :: operates in O(1)-time.
*)

let remove_exact_matches' l_1 l_2 =
    let rec iter l1 l2 left right = 
      match (l1, l2) with
        | ([], []) -> (List.rev left, List.rev right)
        | ([], _) -> 
            failwith "remove_exact_matches': lists of different lengths"
        | (_, []) -> 
            failwith "remove_exact_matches': lists of different lengths"
        | (h1::t1, h2::t2) ->
            if h1 = h2
              then iter t1 t2 ('_' :: left) ('_' :: right)
              else iter t1 t2 (h1 :: left) (h2 :: right)
    in
      iter l_1 l_2 [] []

(*
  The worst-case asymptotic time complexity of this function is also O(n) 
  following the same logic as the other version such that we are iterating 
  through two lists of length n at the same time (O(n)) and performing 
  constant time operations at each iteration.
*)

(* A.3 *)
let find_and_remove_char c l = 
  let rec iter c' l' result =
    match l' with 
      | [] -> None
      | h::t ->
          if h = c
            then Some ((List.rev result) @ ('_' :: t))
            else iter c t (h :: result)
  in 
    iter c l []
(*
  The worst-case asymptotic time complexity of this function is O(n^2) 
  because we simulate iterating through each character in the word input 
  and the operations at each iteration are not necessarily constant-time.  
  Note that List.rev operates in O(N) time on input of length N and @ 
  operates in O(N) time on the left input of length N.  If the matched 
  character is at the end of the word, then List.rev is essentially 
  performed on a list of length (n-1) which is then used in an operation 
  with @.  Thus, we have O(n) * O(n + n) = O(n^2). 
*)

(* A.4 *)
let get_matches target guess = 
  let rec helper t g result =
    match g with
      | [] -> List.rev result
      | h1 :: t1 when h1 = '_' -> helper t t1 ('G' :: result)
      | h1 :: t1 -> match (find_and_remove_char h1 t) with 
                      | None -> helper t t1 ('B' :: result) 
                      | Some s -> helper s t1 ('Y' :: result)
  in
    if List.length target <> List.length guess 
      then failwith "get_matches: lists of different lengths"
      else let (target', guess') = remove_exact_matches target guess in
        helper target' guess' []
(* 
  The worst-case asymptotic time complexity of this function is O(n^3). Let 
  n be the length of the target and guess inputs.  We initially call 
  remove_exact_matches which runs in O(n) time before calling helper which
  essentially has n iterations where find_and_remove_char can be called which
  runs in O(n^2) as established previously.  Thus we have O(n) + O(n * n^2) 
  = O(n^3).
*)

(* A.5 *)
let get_letter_colors target_string guesses_strings = 
  let target = list_of_string target_string in
  let guesses = List.map list_of_string guesses_strings in 
  let color_check col1 col2 = 
    match (col1, col2) with
      | (col1, col2) when col1 = col2 -> col1
      | ('G', _) -> 'G'
      | (_, 'G') -> 'G'
      | ('Y', _) -> 'Y'
      | (_, 'Y') -> 'Y' 
      | (_, _) -> col1 in
  let color_update l col result''' = 
    List.map (fun (x, y) -> 
      if x = l then (x, (color_check col y)) else (x, y)) result''' in
  let compare_color result'' (letter, color) = 
    let prev_matches = List.filter (fun (x, y) -> x = letter) result'' in
    match prev_matches with
      | [] -> (letter, color) :: result''
      | _ -> color_update letter color result'' in 
  let rec compare_colors matches guess result' = 
    match (matches, guess) with
      | ([], []) -> result'
      | ([], _) -> failwith "get_letter_colors: lengths must match"
      | (_, []) -> failwith "get_letter_colors: lengths must match"
      | (h1::t1, h2::t2) -> 
          compare_colors t1 t2 (compare_color result' (h2, h1)) in 
  let rec loop_guesses target' guesses' result =
    match guesses' with 
      | [] -> List.sort compare result
      | h :: t -> loop_guesses target' t 
                    (compare_colors (get_matches target' h) h result)
  in 
    loop_guesses target guesses []

(* A.6 *)
let rec gray_codes n = 
  match n with
    | n when n < 1 -> 
        invalid_arg "gray_codes: input must be greater than 0"
    | 1 -> [[0]; [1]]
    | n -> let g1 = gray_codes (n - 1) in 
        (List.map (fun x -> 0 :: x) g1) @ 
        (List.map (fun x -> 1 :: x) (List.rev g1))

(* B.1 *)
type tree =
  | Leaf
  | Node of int * int * tree * tree  (* depth, value, left/right subtrees *)

(* Depth of an AVL tree. *)
let depth = function
  | Leaf -> 0
  | Node (d, _, _, _) -> d

(* Extract the data value from a node. *)
let data = function
  | Leaf -> failwith "no data"
  | Node (_, v, _, _) -> v

(* Create a new node from two subtrees and a data value.
 * This assumes that the ordering invariant holds i.e.
 * that v is greater than any value in the left subtree
 * and is smaller than any value in the right subtree.  *)
let make_node v l r =
  let d = 1 + max (depth l) (depth r) in  (* compute the correct depth *)
    Node (d, v, l, r)

let rec search i t =
  match t with 
    | Leaf -> false
    | Node (_, v, _, _) when v = i -> true
    | Node (_, v, t1, t2) -> if v > i then search i t1 else search i t2

(* B.2 *)
let left_rotate t =
  match t with
    | Node (d, v, lt, Node (d', v', lt', rt')) -> 
        make_node v' (make_node v lt lt') rt'
    | _ -> failwith "left_rotate: can't left rotate"

let right_rotate t =
  match t with
    | Node (d, v, Node (d', v', lt', rt'), rt) -> 
        make_node v' lt' (make_node v rt rt')
    | _ -> failwith "right_rotate: can't right rotate"

(* B.3 *)
let rec insert v t =
  match t with
    | Leaf -> Node (1, v, Leaf, Leaf)  (* base case *)
    | Node (_, v', l, r) ->
      begin
        match () with
          | _ when v < v' ->   (* insert into left subtree *)
            let l' = insert v l in  (* new left subtree *)
              if depth l' - depth r = 2  (* tree is now unbalanced *)
                then
                  if v < data l'
                    then  (* left-left case *)
                      (* new value v is in the left subtree of l';
                         need to do a right rotation of the new tree *)
                      right_rotate (make_node v' l' r)
                    else  (* left-right case *)
                      (* new value v is in the right subtree of l';
                         need to do a left rotation on l'
                         and a right rotation on the resulting tree. *)
                      right_rotate (make_node v' (left_rotate l') r)
                else
                  make_node v' l' r  (* already balanced *)
          | _ when v > v' ->   (* insert into right subtree *)
            let r' = insert v r in 
              if depth r' - depth l = 2
                then
                  if v < data r'
                    then
                      left_rotate (make_node v' l (right_rotate r'))
                    else
                      left_rotate (make_node v' l r')
                else
                  make_node v' l r' 
          | _ -> t  (* already in tree *)
      end

(* Find the minimum value in an AVL tree. *)
let rec min_avl_tree = function
  | Leaf -> None
  | Node (_, v, l, _) ->
    begin
      match min_avl_tree l with
        | None -> Some v
        | Some l' -> Some l'
    end

(* Find the maximum value in an AVL tree. *)
let rec max_avl_tree = function
  | Leaf -> None
  | Node (_, v, _, r) ->
    begin
      match max_avl_tree r with
        | None -> Some v
        | Some r' -> Some r'
    end

(* Return true if a tree is a valid AVL tree. *)
let rec is_avl_tree = function
  | Leaf -> true
  | Node (d, v, l, r) ->
    let dl = depth l in
    let dr = depth r in
    if is_avl_tree l
      && is_avl_tree r
      && d = 1 + max dl dr
      && abs (dl - dr) < 2
      then  (* check order invariant *)
        match (max_avl_tree l, min_avl_tree r) with
          | (None, None) -> true
          | (None, Some rmin) -> v <= rmin
          | (Some lmax, None) -> v >= lmax
          | (Some lmax, Some rmin) -> v >= lmax && v <= rmin
      else false

(* Convert a tree to a string in "dot" format. *)
let dot_string_of_tree t =
  let sp = Printf.sprintf in
  let rec aux t i =
    match t with
      | Leaf -> (sp "  %d[shape=\"point\",width=0.2]\n" i, i + 1)
      | Node (d, v, l, r) ->
          let (ls, j) = aux l (i + 1) in
          let (rs, k) = aux r j in
          let curr =
            sp "  %d[label=\"%d (d%d)\"]\n" i v d ^
            sp "  %d -> %d\n" i (i + 1) ^
            sp "  %d -> %d\n" i j in
          let body = curr ^ ls ^ rs in
            (body, k)
  in
  let header = "digraph tree {\n" in
  let (body, _) = aux t 0 in
    header ^ body ^ "}\n"

(* Print a tree to a file in "dot" format. *)
let print_dotfile filename t =
  let outfile = open_out (filename ^ ".dot") in
    begin
      Printf.fprintf outfile "%s" (dot_string_of_tree t);
      close_out outfile
    end