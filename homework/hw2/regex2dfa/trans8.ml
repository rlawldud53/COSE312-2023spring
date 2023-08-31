open Regex 

exception Not_implemented

let regex2nfa : Regex.t -> Nfa.t 
=fun regex ->
  let rec regex2nfa2 : Regex.t -> int -> Nfa.t = fun regex switch -> 
    match regex with
    | Empty -> 
        let n1 = Nfa.create_new_nfa () in   
          let (s, n2) =  Nfa.create_state n1 in
            Nfa.add_final_state n2 s
    | Epsilon ->
        let (s, t1) = Nfa.create_state (Nfa.create_new_nfa ()) in
          let n1 = Nfa.add_epsilon_edge  t1 (Nfa.get_initial_state t1 , s )  in
            Nfa.add_final_state n1 s 
    | Alpha a ->
        let s, t1 = Nfa.create_state( Nfa.create_new_nfa () ) in
          let n1 = Nfa.add_edge t1 ( (Nfa.get_initial_state t1, a , s) )  in
            begin match switch with 
            | 1 -> Nfa.add_final_state n1 s 
            | 0 -> n1
            | _ -> Nfa.add_final_state n1 s 
            end
    | OR (t1,t2) -> 
        let n1 = Nfa.create_new_nfa () in
          let new_t1 = regex2nfa2 t1 1 in
            let new_t2 = regex2nfa2 t2 1 in
              let added_states =  BatSet.union (Nfa.get_states (new_t1)) (Nfa.get_states (new_t2 )) in
              (*let _ = prerr_endline ( "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") added_states "")^ " }" ) in*)
                let n2 = Nfa.add_states n1 added_states in 
                  let (s, n3) =  Nfa.create_state n2 in
                    let n4 = begin match switch with 
                    | 1 -> Nfa.add_final_state n3 s 
                    | 0 -> n3
                    | _ -> Nfa.add_final_state n3 s 
                  end
                  in
                    (*let _ = Nfa.print (n4) in*)
                      let n5 = Nfa.add_epsilon_edge n4 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t1) ) in
                        let n6 = Nfa.add_epsilon_edge n5 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t2) ) in
                          let n7 = Nfa.add_epsilon_edge n6 ( BatSet.choose (Nfa.get_final_states (new_t1)) , (*BatSet.choose (Nfa.get_final_states n5)*) s  ) in 
                            let n8 = Nfa.add_epsilon_edge n7 ( BatSet.choose (Nfa.get_final_states (new_t2)) , (*BatSet.choose (Nfa.get_final_states n6)*)s  ) in
                              let n9 = Nfa.add_edges n8 (Nfa.get_edges (new_t1)) in
                                Nfa.add_edges n9 (Nfa.get_edges (new_t2))
    | CONCAT (t1,t2) ->
      (*let n1 = Nfa.create_new_nfa () in*)
      let new_t1 = regex2nfa2 t1 0 in
      (*let _ = Nfa.print(new_t1) in*)
          let new_t2 = regex2nfa2 t2 0 in
            let n1 = Nfa.add_states new_t1 (Nfa.get_states (new_t2)) in
              let array2 = Nfa.get_states new_t2 in
              let n2 = begin match switch with
                | 1 -> Nfa.add_final_state n1 ((*BatSet.choose (Nfa.get_final_states new_t2)*) BatSet.max_elt array2) 
                | 0 -> n1
                | _ -> Nfa.add_final_state n1 ((*BatSet.choose (Nfa.get_final_states new_t2)*) BatSet.max_elt array2) 
              end
              in  
                let n3 = Nfa.add_edges n2 (Nfa.get_edges (new_t2) ) in
                  let array1 = Nfa.get_states new_t1 in
                  let n4 = Nfa.add_epsilon_edge n3 ( (*BatSet.choose (Nfa.get_final_states new_t1)*) BatSet.max_elt array1 , Nfa.get_initial_state new_t2 ) in
                      n4
                  (*let change_final_state : Nfa.t -> Nfa.state -> Nfa.t = fun (states, delta, e_delta, init, final) s -> (states, delta, e_delta, init, BatSet.add s BatSet.Empty ) in
                    let n3 = change_final_state n2 (BatSet.choose (Nfa.get_final_states new_t1)) in 
                      n3*)
                              
    | STAR t -> 
        let n1 = Nfa.create_new_nfa () in
          let new_t = regex2nfa2 t 1 in 
            let n2 = Nfa.add_states n1 (Nfa.get_states (new_t)) in
              let n3 = Nfa.add_edges n2 (Nfa.get_edges (new_t)) in
                let (s, n4) =  Nfa.create_state n3 in
                  let n5 = begin match switch with
                  |1 -> Nfa.add_final_state n4 s
                  |0 -> n4
                  |_ -> Nfa.add_final_state n4 s
                  end
                  in
                    let n6 = Nfa.add_epsilon_edge n5 (Nfa.get_initial_state n4, Nfa.get_initial_state (new_t) ) in
                      let n7 = Nfa.add_epsilon_edge n6 (Nfa.get_initial_state n4, s ) in
                        let n8 = Nfa.add_epsilon_edge n7 ( BatSet.choose (Nfa.get_final_states (new_t)), s ) in
                          let n9 = Nfa.add_epsilon_edge n8 ( BatSet.choose (Nfa.get_final_states (new_t)), Nfa.get_initial_state (new_t) ) in 
                            (*let _ = Nfa.print(n8) in*)
                              n9       
    in 
      let e1  = regex2nfa2 regex 1 in
      (*let _ = Nfa.print e1 in*)
    e1


let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa_t -> 
  (*let eclose_states = BatSet.empty in*)
    let e_closure : Nfa.t -> Nfa.states -> Nfa.states = fun nfa t_states  ->
      let rec sub_e_closure : Nfa.t -> Nfa.states -> int list -> int list = fun nfa_t nfa_states visited ->
        match (BatSet.to_list nfa_states) with
        | [] -> visited
        | hd :: tl ->
          if (List.mem hd visited) then sub_e_closure (nfa_t) (BatSet.of_list tl) visited
          else 
            let next_estates = Nfa.get_next_state_epsilon (nfa_t) hd in
              (*let next_states = Nfa.get_next_state (nfa_t) hd symbol in *)
                if BatSet.is_empty next_estates then sub_e_closure (nfa_t) (BatSet.of_list tl) (hd::visited)
                else sub_e_closure (nfa_t) (BatSet.union (BatSet.of_list tl) next_estates) (hd::visited)
      in BatSet.of_list (sub_e_closure nfa t_states [])  
    in
    let transition_helper : Nfa.t -> alphabet -> Nfa.states -> int list = fun nfa_t symbol states1 ->
      let rec max_epsilon : Nfa.t -> alphabet -> Nfa.states -> int list -> int list -> int list= fun nfa_t symbol states1 visited answer -> (*states에 state1을 넣어서 주면 됨, visitied에도 같이*)
        match (BatSet.to_list states1) with
          | [] -> answer
          | hd :: tl ->
            if List.mem hd visited then max_epsilon nfa_t symbol (BatSet.of_list tl) visited answer
            else
              let next_states = Nfa.get_next_state nfa_t hd symbol in
              let next_estates = Nfa.get_next_state_epsilon nfa_t hd in 
              (*let _ = prerr_endline ( "{  t-hd : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (BatSet.of_list [hd]) "")^ " }" ) in
              let _ = prerr_endline ( "{  next_estates : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (next_estates) "")^ " }" ) in
              let _ = prerr_endline ( "{  next_states : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (next_states) "")^ " }" ) in
              let _ = prerr_endline ( "{  answer : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (BatSet.of_list answer) "")^ " }" ) in*)
                if not (BatSet.is_empty next_states) then 
                  (*let ( (s:int) , (a:alphabet) , (d: (int BatSet.t) ) ) = next_states in*)
                  (*let _ = prerr_endline ( "{ hello1 }" ) in*)
                  max_epsilon nfa_t symbol (BatSet.of_list tl) (hd::visited) ((BatSet.to_list next_states) @ answer)
                else if not (BatSet.is_empty next_estates) then 
                  (*let (s,d) = next_estates in*)
                  (*let _ = prerr_endline ( "{ hello2 }" ) in*)
                  max_epsilon nfa_t symbol (BatSet.union (BatSet.of_list tl) next_estates) (hd::visited) answer
                else
                  (*let _ = prerr_endline ( "{ hello3 }" ) in*)
                  max_epsilon nfa_t symbol (BatSet.of_list tl) (hd::visited) answer
      in
        let answer2 = max_epsilon nfa_t symbol states1 [] [] in
        (*let _ = prerr_endline ( "{  final answer : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (BatSet.of_list answer2) "")^ " }" ) in*)
        answer2
      
    (*let rec check_transition : Nfa.t -> Nfa.state -> list -> list -> alphabet -> int -> list = fun nfa_t start visited answer symbol switch ->
      match visited with
      | [] -> answer
      | hd::tl ->
        let next_states = Nfa.get_next_state nfa_t start symbol in
        let next_estates = Nfa.get_next_state_epsilon nfa_t start in 
          let (s,a) , d = next_states in
            let (s,a) = next_estates in
              if not BatSet.is_empty (next_states) then
                if switch = 1 then check_transition nfa_t *) 
    in
    let d0_closure = e_closure nfa_t ( BatSet.singleton (Nfa.get_initial_state nfa_t) ) in
      let dfa_t = Dfa.create_new_dfa d0_closure in
        let w = BatSet.singleton d0_closure in
          let wlst = BatSet.to_list w in
            let rec nfa2dfa2 : Nfa.t -> Dfa.t -> (int BatSet.t) list -> (int BatSet.t) list -> Dfa.t 
            = fun (nfa_t) (dfa_t) wlst visited ->
              match wlst with
              | [] -> dfa_t
              | hd::tl ->
                (*let _ = prerr_endline ( "{ hd : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (hd) "")^ " }" ) in*)
                let visited2 = [hd]@visited in
                (*let _ = prerr_endline ( "{ ----------------- }" ) in*)
                let trans_lst = BatSet.of_list(transition_helper nfa_t A hd) in
                (*let _ = prerr_endline ( "{ first , trans_lst : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst) "")^ " }" ) in *)
                let trans_lst2 = BatSet.union (e_closure nfa_t trans_lst) trans_lst in
                let trans_lst3 = BatSet.of_list(transition_helper nfa_t B hd) in 
                (*let _ = prerr_endline ( "{ first , trans_lst3 : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst3) "")^ " }" ) in *)
                let trans_lst4 = BatSet.union (e_closure nfa_t trans_lst3) trans_lst3 in
                (*let _ = prerr_endline ( "{ first , trans_lst3 : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst4) "")^ " }" ) in *)
                (*let _ = prerr_endline ( "{ first , trans_lst2 : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst2) "")^ " }" ) in
                let _ = prerr_endline ( "{ first , trans_lst3 : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst2) "")^ " }" ) in
                let _ = prerr_endline ( "{ first , trans_lst4 : " ^ (BatSet.fold (fun s str -> str ^ string_of_int s ^ ", ") (trans_lst2) "")^ " }" ) in*)
                (*let trans_lst42 = [trans_lst2;trans_lst4] in
                let trans_lst43 = trans_lst42 @ tl in*)
                (*let _ = List.iter (fun s -> print_endline (BatSet.to_list s)) trans_lst43 in*)
                if not ((BatSet.is_empty trans_lst) && (BatSet.is_empty trans_lst3 )) then
                  let dfa_t2 = Dfa.add_state dfa_t trans_lst2 in 
                  let dfa_t3 = Dfa.add_edge dfa_t2 ( hd, A, trans_lst2 ) in
                  (*if not (BatSet.is_empty trans_lst3) then*)
                    let dfa_t4 = Dfa.add_state dfa_t3 trans_lst4 in 
                    let dfa_t5 = Dfa.add_edge dfa_t4 ( hd, B, trans_lst4 ) in
                      let f_elem_num = BatSet.cardinal ( BatSet.filter (fun x -> BatSet.mem x (trans_lst2) ) (Nfa.get_final_states (nfa_t) ) ) in
                        if f_elem_num >= 1 then let dfa_t6 = Dfa.add_final_state dfa_t5 trans_lst2 in 
                          let f_elem_num2 = BatSet.cardinal ( BatSet.filter (fun x -> BatSet.mem x (trans_lst4) ) (Nfa.get_final_states (nfa_t) ) ) in 
                            if f_elem_num2 >= 1 then let dfa_t7 = Dfa.add_final_state dfa_t6 trans_lst4 in
                              if (List.mem trans_lst2 visited2) && (List.mem trans_lst4 visited2) then
                                nfa2dfa2 nfa_t dfa_t7 tl visited2
                              else if (List.mem trans_lst2 visited2) then
                                let trans_lst42 = [trans_lst4] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t7 trans_lst43 visited2
                              else if (List.mem trans_lst4 visited2) then
                                let trans_lst42 = [trans_lst2] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t7 trans_lst43 visited2
                              else 
                                let trans_lst42 = [trans_lst2;trans_lst4] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t7 trans_lst43 visited2
                            else 
                              if (List.mem trans_lst2 visited2) && (List.mem trans_lst4 visited2) then
                                nfa2dfa2 nfa_t dfa_t6 tl visited2
                              else if (List.mem trans_lst2 visited2) then
                                let trans_lst42 = [trans_lst4] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                              else if (List.mem trans_lst4 visited2) then
                                let trans_lst42 = [trans_lst2] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                              else 
                                let trans_lst42 = [trans_lst2;trans_lst4] in
                                let trans_lst43 = trans_lst42 @ tl in 
                                nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                        else let f_elem_num2 = BatSet.cardinal ( BatSet.filter (fun x -> BatSet.mem x (trans_lst4) ) (Nfa.get_final_states (nfa_t) ) ) in 
                          if f_elem_num2 >= 1 then let dfa_t6 = Dfa.add_final_state dfa_t5 trans_lst4 in 
                            if (List.mem trans_lst2 visited2) && (List.mem trans_lst4 visited2) then
                              nfa2dfa2 nfa_t dfa_t6 tl visited2
                            else if (List.mem trans_lst2 visited2) then
                              let trans_lst42 = [trans_lst4] in
                              let trans_lst43 = trans_lst42 @ tl in
                              nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                            else if (List.mem trans_lst4 visited2) then
                              let trans_lst42 = [trans_lst2] in
                              let trans_lst43 = trans_lst42 @ tl in 
                              nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                            else 
                              let trans_lst42 = [trans_lst2;trans_lst4] in
                              let trans_lst43 = trans_lst42 @ tl in 
                              nfa2dfa2 nfa_t dfa_t6 trans_lst43 visited2
                          else 
                            if (List.mem trans_lst2 visited2) && (List.mem trans_lst4 visited2) then
                              nfa2dfa2 nfa_t dfa_t5 tl visited2
                            else if (List.mem trans_lst2 visited2) then
                              let trans_lst42 = [trans_lst4] in
                              let trans_lst43 = trans_lst42 @ tl in 
                              nfa2dfa2 nfa_t dfa_t5 trans_lst43 visited2
                            else if (List.mem trans_lst4 visited2) then
                              let trans_lst42 = [trans_lst2] in
                              let trans_lst43 = trans_lst42 @ tl in 
                              nfa2dfa2 nfa_t dfa_t5 trans_lst43 visited2
                            else 
                              let trans_lst42 = [trans_lst2;trans_lst4] in
                              let trans_lst43 = trans_lst42 @ tl in 
                              nfa2dfa2 nfa_t dfa_t5 trans_lst43 visited2
                else nfa2dfa2 nfa_t dfa_t (tl) visited2
                    (*else then 
                    let dfa_t2 = Dfa.add_state dfa_t trans_lst2 in 
                    let dfa_t3 = Dfa.add_edge dfa_t2 ( hd, A, trans_lst2 ) in
                      let f_elem_num = BatSet.cardinal ( BatSet.filter (fun x -> BatSet.mem x (trans_lst2) ) (Nfa.get_final_states (nfa_t) ) ) in
                        if f_elem_num >= 1 then let dfa_t4 = Dfa.add_final_state dfa_t3 trans_lst2 in nfa2dfa2 nfa_t dfa_t4 (trans_lst2::tl)
                        else nfa2dfa2 nfa_t dfa_t3 (trans_lst2::tl)
                  else nfa2dfa2 nfa_t dfa_t (tl)*)
    in let res =  nfa2dfa2 nfa_t dfa_t wlst []
    (*in let _ = Dfa.print res*)
  in res
    

(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
= fun dfa_t symbol_lst -> 
  let rec check_acceptable : Dfa.t -> ((Nfa.state) BatSet.t) -> alphabet list -> bool 
  = fun (dfa_t) (start) symbol_lst2 -> 
    match symbol_lst2 with 
    | [] -> 
      if (Dfa.is_final_state dfa_t start) then true
      else false
    | hd::tl ->
      let symbol_to_go = hd in
      let next_state_to_go = Dfa.get_next_state (dfa_t) (start) (symbol_to_go) in
      try
        if (BatSet.is_empty next_state_to_go) then false
        else check_acceptable dfa_t next_state_to_go tl 
      with _ -> false
  in check_acceptable dfa_t (Dfa.get_initial_state dfa_t) symbol_lst
