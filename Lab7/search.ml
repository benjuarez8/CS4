(* search.ml: search strategies *)
(* Student name: Benjamin Juarez *)
(* CMS cluster login name: bjuarez *)

module type Storage =
  sig
    type 'a t
    exception Empty

    val create : unit -> 'a t
    val push : 'a -> 'a t -> unit
    val pop : 'a t -> 'a
    val is_empty : 'a t -> bool
  end

module type Domain =
  sig
    type t
    val show : t -> string
    val is_solved : t -> bool
    val compare : t -> t -> int
    val next : t -> t list
  end

module Search (S : Storage) (D : Domain) =
  struct
    module DS = Set.Make(D)

    let search init = 
      let storage = S.create() in 
      let rec iter visited = 
        if S.is_empty storage then 
          raise Not_found
        else
          let history = S.pop storage in 
          let most_recent_board = List.hd history in 
          if DS.mem most_recent_board visited 
            then iter visited 
          else if D.is_solved most_recent_board 
            then history
          else
            let new_visited = DS.add most_recent_board visited in
            let children = D.next most_recent_board in 
            begin
              List.iter (fun x -> S.push (x :: history) storage) children;
              iter new_visited
            end
      in
        begin
          S.push [init] storage;
          iter DS.empty 
        end

    let show_history hist =
      (String.concat "\n----\n\n" (List.map D.show (List.rev hist))) ^ "\n"
  end

