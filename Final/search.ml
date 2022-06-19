(* Student name: Benjamin Juarez *)
(* Email: bjuarez@caltech.edu *)

open Storage
open Board
open Utils

exception Solution_not_found

module type Searcher =
  sig
    val search : int -> int -> int -> int -> bool -> (Loc.t list) option
  end

module Make (S : Storage) : Searcher =
  struct
    module B = Board.Make(S)
    module P = Print(B)

    (* Helper functions go here. *)

    let search nrows ncols start_row start_col print =
      let compute_min_reachability loc_counts = 
        let rec cmr_iter counts min_count = 
          match counts with 
            | [] -> min_count
            | h :: t -> let i = snd h in 
                match i with 
                  | _ when i < min_count -> cmr_iter t i 
                  | _ -> cmr_iter t min_count
        in 
          let min_init = snd (List.hd loc_counts) in 
            cmr_iter loc_counts min_init
      in 
      let collect_locs loc_counts min_count = 
        let rec cl_iter counts locs = 
          match counts with 
            | [] -> locs 
            | h :: t -> let i = snd h in 
                match i with 
                  | _ when i = min_count -> let loc = fst h in 
                                            cl_iter t (loc :: locs)
                  | _ -> cl_iter t locs 
        in 
          cl_iter loc_counts []
      in 
      let rec iter board locs = 
        if B.is_solved board then 
          if print then 
            begin
              P.print_board board true;
              Some (List.rev locs)
            end
          else
            Some (List.rev locs)
        else
          let last_loc = B.get_last board in 
          let loc_counts = B.get_loc_counts_from_loc board last_loc in 
            if loc_counts = [] then 
              None
            else
              let min_reach_count = compute_min_reachability loc_counts in 
              let locs_w_min_count = collect_locs loc_counts min_reach_count in
              let num_locs = List.length locs_w_min_count in 
              let rand_idx = Random.int num_locs in 
              let next_loc = List.nth locs_w_min_count rand_idx in 
              let next_board = B.place board next_loc in 
                iter next_board (next_loc :: locs)
      in     
      let board = B.place (B.make nrows ncols) (start_row, start_col) in 
        iter board [(start_row, start_col)]
  end

