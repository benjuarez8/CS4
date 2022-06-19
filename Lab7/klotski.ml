(* klotski.ml: core functionality of the Klotski game. *)
(* Student name: Benjamin Juarez *)
(* CMS cluster login name: bjuarez *)

(* ---------------------------------------------------------------------- 
 * Types.
 * ---------------------------------------------------------------------- *)

type loc = int * int
type dir = Up | Down | Left | Right
type move = char * dir * int

module LocM =
  struct
    type t = loc
    let compare = Stdlib.compare
  end

module LocSet : Set.S with type elt = loc = Set.Make(LocM)

(* Sets of LocSets.  Used locally only. *)

module LocSetM =
  struct
    type t = LocSet.t
    let compare = LocSet.compare
  end

module LocSetSet = Set.Make(LocSetM)

module CharM =
  struct
    type t = char
    let compare = Stdlib.compare
  end

module CharMap : Map.S with type key = char = Map.Make(CharM)

type piece = LocSet.t
type t = { pieces : piece CharMap.t ; unoccupied : LocSet.t }

(* ---------------------------------------------------------------------- 
 * Functions.
 * ---------------------------------------------------------------------- *)

(* Create a board from a string. *)
let read s = 
  let rec iter p u r c =
    match () with
      | _ when r = 5 -> { pieces = p; unoccupied = u }
      | _ when c = 4 -> iter p u (r + 1) 0 
      | _ -> 
        let i = r * 4 + c in
        let ch = s.[i] in
          if ch = '.'  (* unoccupied location; add to unoccupied set *)
            then iter p (LocSet.add (r, c) u) r (c + 1)
            else  (* occupied; add to appropriate piece set *)
              try
                let cs  = CharMap.find ch p in     (* old piece set *)
                let cs' = LocSet.add (r, c) cs in  (* add new location *)
                let p'  = CharMap.add ch cs' p in  (* store back into map *)
                  iter p' u r (c + 1)
              with
                Not_found ->  (* new piece; create a new piece set *)
                  let cs = LocSet.singleton (r, c) in
                  let p' = CharMap.add ch cs p in
                    iter p' u r (c + 1)
  in
    if String.length s <> 20
      then failwith "read: invalid input string length"
      else iter CharMap.empty LocSet.empty 0 0

(* Convert the board to a string representation suitable for printing. *)
let show b = 
  let string_of_char_list = function
    | [a;b;c;d] -> Printf.sprintf "%c%c%c%c" a b c d
    | _ -> failwith "invalid char list"
  in
  let char_at board loc =
    let rec iter = function
      | [] -> raise Not_found
      | (c, locs) :: t -> 
        if LocSet.mem loc locs then c else iter t
    in
    if LocSet.mem loc board.unoccupied
      then '.'
      else iter (CharMap.bindings board.pieces)
  in
  (String.concat "\n"
     (List.map (fun r ->
        string_of_char_list
          (List.map (char_at b) 
            (List.map (fun c -> (r, c)) [0; 1; 2; 3])))
        [0; 1; 2; 3; 4])) ^ "\n"

let is_solved b = 
  let solved_loc = LocSet.of_list [(3,1); (3,2); (4,1); (4,2)] in
    CharMap.exists (fun x y -> (LocSet.equal y solved_loc)) b.pieces

let compare_helper b = 
  let result_start = LocSetSet.empty in 
  let rec iter b result = 
    match b with 
      | [] -> result
      | (_, locs) :: t -> iter t (LocSetSet.add locs result)
  in iter b result_start

let compare b1 b2 = 
  let pieces1 = CharMap.bindings b1.pieces in
  let pieces2 = CharMap.bindings b2.pieces in
  let unoccupied_check = LocSet.compare b1.unoccupied b2.unoccupied in
    match unoccupied_check with
      | 1 -> 1
      | -1 -> -1
      | _ -> 
          LocSetSet.compare (compare_helper pieces1) (compare_helper pieces2)

let remove c ({ pieces = p; unoccupied = u } as b) = 
  if CharMap.mem c p then 
    let new_u = LocSet.union u (CharMap.find c p) in
    { pieces = CharMap.remove c p; unoccupied = new_u }
  else
    b

let add (c, p) { pieces = ps; unoccupied = u } = 
  if (LocSet.subset p u) && (not (CharMap.mem c ps)) then 
    Some { pieces = (CharMap.add c p ps); unoccupied = (LocSet.diff u p) }
  else
    None

let move_helper piece_label direction board =
  let get_new_locs locs = 
    match direction with 
      | Up -> 
          LocSet.map (fun (row_idx, col_idx) -> (row_idx - 1, col_idx)) locs
      | Down -> 
          LocSet.map (fun (row_idx, col_idx) -> (row_idx + 1, col_idx)) locs
      | Left -> 
          LocSet.map (fun (row_idx, col_idx) -> (row_idx, col_idx - 1)) locs
      | Right -> 
          LocSet.map (fun (row_idx, col_idx) -> (row_idx, col_idx + 1)) locs in
  let new_locs = get_new_locs (CharMap.find piece_label board.pieces) in 
    add (piece_label, new_locs) (remove piece_label board)

let make_move (c, d, i) b =
  if (not (CharMap.mem c b.pieces)) || i < 1 then
    None
  else
    let rec iter (c', d', i') b' = 
      match i' with 
        | 0 -> Some b'
        | _ -> match move_helper c' d' b' with 
                | None -> None
                | Some board -> iter (c', d', (i' - 1)) board
    in iter (c, d, i) b 

let next b =
  let pieces = CharMap.bindings b.pieces in 
  let rec iter pieces i direction result = 
    match pieces with 
      | [] -> result
      | (c, p) ::t -> if i = 0 then iter t 4 direction result else
          match make_move (c, direction, i) b with
            | Some board -> iter pieces (i - 1) direction (board :: result)
            | None -> iter pieces (i - 1) direction result
  in 
  (iter pieces 4 Up []) @ (iter pieces 4 Down []) @
  (iter pieces 4 Left []) @ (iter pieces 4 Right [])

(* Function to interactively test the "next" function. 
 * Useful for debugging. *)
let test_next b =
  let bs = next b in
    begin
      print_string (show b ^ "\n");
      List.iter 
        (fun b -> print_string ("----\n\n" ^ show b ^ "\n"))
        bs
    end

