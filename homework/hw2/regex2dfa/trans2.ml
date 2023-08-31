open Regex 

exception Not_implemented

let regex2nfa : Regex.t -> Nfa.t 
=fun regex ->
    let rec reg2nfa2 : Regex.t -> Nfa.t = fun regex -> 
    match regex with
    | Empty -> n3 in
        let n1 = create_new_nfa () in   
          let (s, n2) =  Nfa.create_state n1 in
            let n3 = Nfa.add_final_state n2 s
    | Epsilon -> n in 
        let (s, t1) = Nfa.create_state create_new_nfa () in
          let n1 = Nfa.add_epsilon_edge  t1 (Nfa.get_initial_state t1, BatSet.of_list [s] )  in
            let n = Nfa.add_final_stat  n1, s 
    | Alpha a -> n in 
        let s, t1 = Nfa.create_state( create_new_nfa () ) in
          let n1 = Nfa.add_edge t1 ( (Nfa.get_initial_state t1,a) , BatSet.of_list [s] )  in
            let n = Nfa.add_final_state n1 s 
    | OR (t1,t2) -> n9 in
        let n1 = create_new_nfa () in
          let added_states =  BatSet.union (Nfa.get_states (regex2nfa t1)) (Nfa.get_states (regex2nfa t2 )) in
            let _ = prerr_endline (added_states) in
            let n2 = Nfa.add_states n1 added_states in 
              let (s, n3) =  Nfa.create_state n2 in
                let n4 = Nfa.add_final_state n3 s in
                  let n5 = Nfa.add_epsilon_edge n4 (Nfa.get_initial_state n4, BatSet.of_list [Nfa.get_initial_state (regex2nfa t1), Nfa.get_initial_state (regex2nfa t2)] ) in
                    let n6 = Nfa.add_epsilon edge n5 ( BatSet.choose (Nfa.get_final_states (regex2nfa t1)) , Nfa.get_final_states n5  ) in 
                      let n7 = Nfa.add_epsilon edge n6 ( BatSet.choose (Nfa.get_final_states (regex2nfa t2)) , Nfa.get_final_states n6  ) in
                        let n8 = Nfa.add_edges n7 (get_edges (regex2nfa t1)) in
                          let n9 = Nfa.add_eges n8 (get_edges (regex2nfa t2)) in
    | CONCAT (t1,t2) -> n7 in
      let n1 = create_new_nfa () in
        let added_states =  BatSet.union (Nfa.get_states (regex2nfa t1)) (Nfa.get_states (regex2nfa t2 )) in
          let n2 = Nfa.add_states n1 added_states in
            let (s, n3) =  Nfa.create_state n2 in
              let n4 = Nfa.add_final_state n3 s in
                let n5 = Nfa.add_epsilon_edge n4 ( BatSet.choose (Nfa.get_final_states (regex2nfa t1)) , BatSet.of_list [Nfa.get_initial_state (regex2nfa t2)] ) in
                  let n6 = Nfa.add_edges n5 (get_edges (regex2nfa t1)) in
                    let n7 = = Nfa.add_edges n6 (get_edges (regex2nfa t2)) 
    | STAR t -> n8 in
        let n1 = Nfa.create_new_nfa () in
          let n2 = Nfa.add_states n1 (Nfa.get_states (regex2nfa t)) in
            let (s, n3) =  Nfa.create_state n2 in
              let n4 = Nfa.add_final_state n3 s in
                let n5 = Nfa.add_epsilon_edge n4 (Nfa.get_initial_state n4, BatSet.of_list [Nfa.get_initial_state (regex2nfa t)] ) in
                  let n6 = Nfa.add_epsilon_edge n5 (Nfa.get_initial_state n4, Nfa.get_final_states n5 ) in
                    let n7 = Nfa.add_epsilon_edge n6 ( BatSet.choose (Nfa.get_final_states (regex2nfa t)), Nfa.get_final_states n5 ) in
                      let n8 =  Nfa.add_epsilon_edge n6 ( BatSet.choose (Nfa.get_final_states (regex2nfa t)), BatSet.of_list [Nfa.get_initial_state (regex2nfa t)] )


      
      


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
