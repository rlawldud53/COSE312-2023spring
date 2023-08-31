exception NotImplemented;;

let rec sum : int list -> int =
  fun list ->
    match list with
    | [] -> 0
    | hd::tl -> hd + (sum tl);;

let rec map f l =
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl);;


let suml: int list list -> int
= fun list -> sum (map sum list);; (* TODO *)

