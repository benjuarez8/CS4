(* Student name: Benjamin Juarez *)
(* Email: bjuarez@caltech.edu *)

module Loc =
  struct
    type t = int * int

    let compare = Stdlib.compare
  end

module type Storage =
  sig
    type t
    type loc = Loc.t

    val make    : int -> int -> t
    val get     : t -> loc -> int option
    val set     : t -> loc -> int -> t
    val has_loc : t -> loc -> bool
    val remove  : t -> loc -> t
  end

(*
 * Imperative implementation.
 * The data representation is an array of arrays of integers.
 * A null location is represented by the number -1 stored at the location.
 *)
module ImpStorage : Storage =
  struct
    type t   = int array array
    type loc = Loc.t

    let make nrows ncols = 
      if nrows > 0 && ncols > 0 then 
        Array.make_matrix nrows ncols (-1)
      else
        invalid_arg (Printf.sprintf 
        "make: invalid arguments: nrows = %d, ncols = %d" nrows ncols)

    let get data (row, col) = 
      let num_rows = Array.length data in 
      let num_cols = Array.length data.(0) in
      if row < 0 || row >= num_rows then 
        None
      else if col < 0 || col >= num_cols then 
        None
      else if data.(row).(col) = -1 then 
        None
      else
        Some (data.(row).(col))

    let set data (row, col) i = 
      if i < 0 then 
        invalid_arg "set: negative argument"
      else
        try 
          begin
            data.(row).(col) <- i;
            data
          end
        with 
          Invalid_argument _ -> invalid_arg (Printf.sprintf 
          "set: invalid location: (%d, %d)" row col)

    let has_loc data (row, col) =
      if get data (row, col) = None then 
        false
      else
        true

    let remove data (row, col) =
      if get data (row, col) = None then 
        data
      else
        begin
          data.(row).(col) <- (-1);
          data
        end
  end

(*
 * Functional implementation.
 * The data representation is a map between locs and integers.
 * A null location is represented by the absence of the loc in the map.
 *)
module FunStorage : Storage =
  struct
    module LocMap = Map.Make(Loc)

    type t = 
      {
        contents : int LocMap.t;
        nrows    : int;
        ncols    : int
      }

    type loc = Loc.t

    let make nrows ncols = 
      if nrows > 0 && ncols > 0 then 
        { contents = LocMap.empty; nrows = nrows; ncols = ncols }
      else
        invalid_arg (Printf.sprintf 
        "make: invalid arguments: nrows = %d, ncols = %d" nrows ncols)
    
    let get data (row, col) = 
      if LocMap.mem (row, col) data.contents then 
        Some (LocMap.find (row, col) data.contents)
      else
        None

    let set data (row, col) i = 
      if i < 0 then 
        invalid_arg "set: negative argument"
      else if row < 0 || row >= data.nrows then 
        invalid_arg (Printf.sprintf "set: invalid location: (%d, %d)" row col)
      else if col < 0 || col >= data.ncols then 
        invalid_arg (Printf.sprintf "set: invalid location: (%d, %d)" row col)
      else
        { data with contents = LocMap.add (row, col) i data.contents }

    let has_loc data (row, col) = 
      LocMap.mem (row, col) data.contents

    let remove data (row, col) =
      { data with contents = LocMap.remove (row, col) data.contents }
  end

