open Regex 

exception Not_implemented

let regex2nfa : Regex.t -> Nfa.t 
=fun regex ->
  let rec regex2nfa2 : Regex.t -> Nfa.t = fun regex -> 
    match regex with
    | Empty -> 
        let n1 = Nfa.create_new_nfa () in   
          let (s, n2) =  Nfa.create_state n1 in
            Nfa.add_final_state n2 s
    | Epsilon ->
        let (s, t1) = Nfa.create_state (Nfa.create_new_nfa ()) in
          let n1 = Nfa.add_epsilon_edge  t1 (Nfa.get_initial_state t1 , s )  in
            Nfa.add_final_state  n1 s 
    | Alpha a ->
        let s, t1 = Nfa.create_state( Nfa.create_new_nfa () ) in
          let n1 = Nfa.add_edge t1 ( (Nfa.get_initial_state t1, a , s) )  in
            Nfa.add_final_state n1 s 
    | OR (t1,t2) -> 
        let n1 = Nfa.create_new_nfa () in
          let new_t1 = regex2nfa2 t1 in
            let new_t2 = regex2nfa2 t2 in
              let added_states =  BatSet.union (Nfa.get_states (new_t1)) (Nfa.get_states (new_t2 )) in
              (*let _ = prerr_endline ( "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") added_states "")^ " }" ) in*)
                let n2 = Nfa.add_states n1 added_states in 
                  let (s, n3) =  Nfa.create_state n2 in
                    let n4 = Nfa.add_final_state n3 s in
                    (*let _ = Nfa.print (n4) in*)
                      let n5 = Nfa.add_epsilon_edge n4 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t1) ) in
                        let n6 = Nfa.add_epsilon_edge n5 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t2) ) in
                          let n7 = Nfa.add_epsilon_edge n6 ( BatSet.choose (Nfa.get_final_states (new_t1)) , BatSet.choose (Nfa.get_final_states n5)  ) in 
                            let n8 = Nfa.add_epsilon_edge n7 ( BatSet.choose (Nfa.get_final_states (new_t2)) , BatSet.choose (Nfa.get_final_states n6)  ) in
                              let n9 = Nfa.add_edges n8 (Nfa.get_edges (new_t1)) in
                                Nfa.add_edges n9 (Nfa.get_edges (new_t2))
    | CONCAT (t1,t2) ->
      (*let n1 = Nfa.create_new_nfa () in*)
      let new_t1 = regex2nfa2 t1 in
      let new_t2 = regex2nfa2 t2 in
      (*let excluded_elem = Nfa.get_initial_state new_t1 in
      let create_new_nfa2 : (unit -> Nfa.t) = fun unit -> (BatSet.singleton excluded_elem, BatMap.empty, BatMap.empty, excluded_elem, BatSet.empty) in*)
      let n1 = create_new_nfa2() in
              let added_states =  BatSet.union (Nfa.get_states (new_t1)) (Nfa.get_states (new_t2 )) in
                let filtered_set = BatSet.filter (fun x -> x <> excluded_elem) added_states in
                  let n2 = Nfa.add_states n1 filtered_set in
                  (*let (s, n3) =  Nfa.create_state n2 in*)
                    let n4 = Nfa.add_final_state n2 (BatSet.choose (Nfa.get_final_states new_t2)) in
                      let n5 = Nfa.add_epsilon_edge n4 ( BatSet.choose (Nfa.get_final_states (new_t1)) , Nfa.get_initial_state (new_t2) ) in
                        (*let delta_lst, edelta_lst = Nfa.get_edges (new_t1) in
                          let delta_lst2 = List.filter (fun (k, _ ) -> k <> (excluded_elem,"a") ) delta_lst in
                            let edelta_lst2 = List.filter ( fun (k, _ ) -> k <> excluded_elem) edelta_lst in*)
                          (*let delta_lst2 = BatMap.remove_all ("(" ^ string_of_int (Nfa.get_initial_state new_t1) ^ ",a)") (BatMap.of_list delta_lst)  in
                            let delta_lst3 = BatMap.remove_all ("(" ^ string_of_int (Nfa.get_initial_state new_t1) ^ ",b)") (BatMap.of_list delta_lst2) in
                              let edelta_lst2 = BatMap.remove_all (string_of_int (Nfa.get_initial_state new_t1) ) edelta_lst in*)
                                let n6 = Nfa.add_edges n5 ( (delta_lst2, edelata_lst2) ) in
                                  let n7 = Nfa.add_edges n6 (Nfa.get_edges (new_t2)) in
                              n7 
    | STAR t -> 
        let n1 = Nfa.create_new_nfa () in
          let new_t = regex2nfa2 t in 
            let n2 = Nfa.add_states n1 (Nfa.get_states (new_t)) in
                let (s, n3) =  Nfa.create_state n2 in
                  let n4 = Nfa.add_final_state n3 s in
                    let n5 = Nfa.add_epsilon_edge n4 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t) ) in
                      let n6 = Nfa.add_epsilon_edge n5 (Nfa.get_initial_state n4, BatSet.choose (Nfa.get_final_states n5) ) in
                        let n7 = Nfa.add_epsilon_edge n6 ( BatSet.choose (Nfa.get_final_states (new_t)), BatSet.choose (Nfa.get_final_states n5) ) in
                          let n8 = Nfa.add_epsilon_edge n7 ( BatSet.choose (Nfa.get_final_states (new_t)), Nfa.get_initial_state (new_t) ) in 
                            let _ = Nfa.print(n8) in
                              n8        
    in 
      let _ = Nfa.print(regex2nfa2 regex)                                     
    in regex2nfa2 regex   


      
      


let nfa2dfa : Nfa.t -> Dfa.t
=fun _ -> raise Not_implemented (* TODO *)
 
(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
=fun _ _ -> raise Not_implemented (* TODO *)
