exception NotImplemented;;

let rec binarize_2 : int -> int list -> int list =
  fun n l ->
    if n <= 1 then n::l
    else binarize_2 (n/2) ((n mod 2)::l);;

let binarize : int -> int list
= fun n -> binarize_2 n [];; (* TODO *)
