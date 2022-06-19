(* Student name: Benjamin Juarez *)
(* Email: bjuarez@caltech.edu *)

open Storage

(*
 * Helper functions.
 *)

(* Return `true` if a loc is valid on a board of size
 * `nrows` rows by `ncols` columns. *)
let ok_loc nrows ncols (row, col) =
  row >= 0 && row < nrows && col >= 0 && col < ncols

(* Raise an `Invalid_argument` exception due to a bad location.
 * `name` is the name of the function, and `cause` is the
 * reason for the argument being bad. *)
let bad_loc name cause (row, col) =
  let msg = 
    Printf.sprintf "%s: %s;  row = %d col = %d%!" 
      name cause row col
  in
    invalid_arg msg


(*
 * The board module type and module.  
 * It represents the state of the knight's tour solution.
 *)

module type Board =
  sig
    type loc = Loc.t
    type t

    val make                    : int -> int -> t
    val get_dimensions          : t -> int * int
    val get_last                : t -> loc
    val get_index               : t -> loc -> int option
    val get_reachable           : t -> loc -> int option
    val get_loc_counts_from_loc : t -> loc -> (loc * int) list
    val place                   : t -> loc -> t
    val undo                    : t -> t
    val is_solved               : t -> bool
    val get_placed              : t -> loc list
  end

module Make (S: Storage) : Board =
  struct
    type loc = Loc.t

    type t = 
      {
        nrows      : int;
        ncols      : int;
        size       : int;       (* total # of squares on board *)
        placed     : loc list;  (* locations of all knights placed on board *)
        last_index : int;       (* index of last knight placed *)
        indices    : S.t;
        reachable  : S.t
      }

    (* Helper functions. *)

    let check_bounds board loc = 
      ok_loc board.nrows board.ncols loc

    let init_reachable nrows ncols =
      let knight_moves = 
        [(1,2);(2,1);(-1,-2);(-2,-1);(1,-2);(-2,1);(-1,2);(2,-1)] 
      in 
      let rec get_count r c moves count = 
        match moves with 
          | [] -> count 
          | (dr, dc) :: t -> let new_r = r + dr in let new_c = c + dc in 
              if ok_loc nrows ncols (new_r, new_c) then 
                get_count r c t (count + 1)
              else
                get_count r c t count
      in
      let rec iter r c s_grid = 
        if c = ncols then 
          s_grid
        else if r = nrows then
          iter 0 (c + 1) s_grid
        else
          let i = get_count r c knight_moves 0 in 
          let grid_update = S.set s_grid (r, c) i in
            iter (r + 1) c grid_update
      in 
        let storage_grid = S.make nrows ncols in 
          iter 0 0 storage_grid

    (* Interface functions. *)

    let make nrows ncols = 
      {
        nrows      = nrows;
        ncols      = ncols;
        size       = nrows * ncols;
        placed     = [];
        last_index = 0;
        indices    = S.make nrows ncols;
        reachable  = init_reachable nrows ncols
      }

    let get_dimensions board =
      (board.nrows, board.ncols)

    let get_last board =
      match board.placed with
        | [] -> raise Not_found
        | h :: _ -> h

    let get_index board loc = 
      if not (check_bounds board loc) then
        bad_loc "get_index" "location off board" loc
      else
        S.get board.indices loc

    let get_reachable board loc = 
      if not (check_bounds board loc) then
        bad_loc "get_reachable" "location off board" loc
      else
        S.get board.reachable loc

    let get_loc_counts_from_loc board loc = 
      if not (check_bounds board loc) then 
        bad_loc "get_loc_counts_from_loc" "location off board" loc
      else
        let knight_moves = 
          [(1,2);(2,1);(-1,-2);(-2,-1);(1,-2);(-2,1);(-1,2);(2,-1)] 
        in 
        let get_locs board (r, c) = 
          let rec get_locs_iter moves locs = 
            match moves with 
              | [] -> locs
              | (dr, dc) :: t -> let loc = (r + dr, c + dc) in 
                  if check_bounds board loc then 
                    let add_loc = (loc :: locs) in 
                    get_locs_iter t add_loc
                  else
                    get_locs_iter t locs
          in
            get_locs_iter knight_moves []  
        in 
        let rec iter locations result = 
          match locations with 
            | [] -> result
            | (r, c) :: t -> let curr_loc = (r, c) in 
              match get_reachable board curr_loc with 
                | Some i -> iter t ((curr_loc, i) :: result)
                | None -> iter t result
        in 
          let locs = get_locs board loc in 
            iter locs [] 
    
    let place board loc = 
      if not (check_bounds board loc) then 
        bad_loc "place" "location off board" loc 
      else if get_index board loc <> None then 
        bad_loc "place" "location already occupied by Knight" loc 
      else
        let check_move loc = 
          let (prev_r, prev_c) = get_last board in 
          let curr_r = fst loc in 
          let curr_c = snd loc in 
          let dr = abs (curr_r - prev_r) in 
          let dc = abs (curr_c - prev_c) in 
            not ((dr = 2 && dc == 1) || (dr == 1 && dc == 2)) 
        in 
        if board.last_index <> 0 && check_move loc then 
          bad_loc "place" "location isn't Knight's move away" loc 
        else
          let new_placed = (loc :: board.placed) in 
          let new_last_idx = board.last_index + 1 in 
          let new_indices = S.set board.indices loc new_last_idx in 
          let get_locs board (r, c) = 
            let knight_moves = 
              [(1,2);(2,1);(-1,-2);(-2,-1);(1,-2);(-2,1);(-1,2);(2,-1)] in 
            let rec get_locs_iter moves locs = 
              match moves with 
                | [] -> locs
                | (dr, dc) :: t -> let loc = (r + dr, c + dc) in 
                    if check_bounds board loc then 
                      let add_loc = (loc :: locs) in 
                      get_locs_iter t add_loc
                    else
                      get_locs_iter t locs
            in
              get_locs_iter knight_moves []
          in 
          let rec update_reachable locations grid = 
            match locations with 
              | [] -> grid 
              | (r, c) :: t -> 
                match get_reachable board (r, c) with
                  | Some i -> update_reachable t (S.set grid (r, c) (i - 1))
                  | None -> update_reachable t grid
          in 
            let grid = S.remove board.reachable loc in 
            let locs = get_locs board loc in 
            let new_reachable = update_reachable locs grid in 
              { board with placed = new_placed; last_index = new_last_idx; 
                indices = new_indices; reachable = new_reachable }

    let undo board = 
      if board.last_index = 0 then 
        board
      else
        let new_placed = List.tl board.placed in 
        let new_last_idx = board.last_index - 1 in 
        let new_indices = S.remove board.indices (List.hd board.placed) in 
        let get_locs board (r, c) = 
          let knight_moves = 
            [(1,2);(2,1);(-1,-2);(-2,-1);(1,-2);(-2,1);(-1,2);(2,-1)] in 
          let rec get_locs_iter moves locs = 
            match moves with 
              | [] -> locs
              | (dr, dc) :: t -> let loc = (r + dr, c + dc) in 
                  if check_bounds board loc then 
                    let add_loc = (loc :: locs) in 
                    get_locs_iter t add_loc
                  else
                    get_locs_iter t locs
          in
            get_locs_iter knight_moves []
        in 
        let rec get_count moves count = 
          match moves with 
            | [] -> count 
            | (r, c) :: t ->  
                if get_index board (r, c) = None then 
                  get_count t (count + 1)
                else
                  get_count t count
        in
        let rec update_reachable locations grid = 
          match locations with 
            | [] -> grid 
            | (r, c) :: t -> 
              match get_reachable board (r, c) with
                | Some i -> update_reachable t (S.set grid (r, c) (i + 1))
                | None -> update_reachable t grid
        in 
          let last = List.hd board.placed in 
          let locs = get_locs board last in 
          let count = get_count locs 0 in 
          let new_reachable = update_reachable locs (S.set board.reachable 
                                last count) in 
            { board with placed = new_placed; last_index = new_last_idx; 
              indices = new_indices; reachable = new_reachable }

    let is_solved board = board.last_index = board.size
    let get_placed board = List.rev board.placed
  end
