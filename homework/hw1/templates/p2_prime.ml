exception NotImplemented;;


let rec check_prime : int -> int -> bool 
= fun a n -> 
    if a = 1 then true else
    (if (n mod a = 0) then false else (check_prime (a-1) n))  ;; (* TODO *)

let prime : int -> bool
= fun n ->
  if n =1 then false
  else check_prime (n-1) n;;
