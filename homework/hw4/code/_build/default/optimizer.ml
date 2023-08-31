type e1 = int*int
type edge = e1 list
type def = string list
type use = string list
type in1 = string list
type out = string list
type oi = out*in1
type in_out = int*oi
type du = def*use
type def_use = int*du
type def_block = string*int list
type block = int * Spvm.program
type dead_code_location = int*string
type leader_block = int * Spvm.linstr

exception Not_Implemented of string 

let optimize : Spvm.program -> Spvm.program = fun pgm ->(*-> pgm*)

  (* 기타 함수 *)
  (*let get_def_from_du : du -> def = fun du ->
    match du with
    | (def,_) -> def
    | _ -> raise (Not_Implemented "not du")
  in*)
  (*let get_def_from_du : du -> def = fun du ->
    let (def,_) = du in
      def
  in

  let get_use_from_du : du -> def = fun du ->
    let (_,use) = du in
      use
  in*)

  (*let get_instr : Spvm.linstr -> Spvm.instr = fun l ->
    let (_, instr) = l in
    instr

  in*)
  (*let print_block_label : block -> _ = fun b -> 
    let (label,_) = b in
    let _ = print_int label in
    print_string "\n" 
  in*)
  let get_second_from_linstr : Spvm.linstr -> Spvm.instr = fun l ->
    let (_, lin) = l in
    lin
  in
  (*let get_fisrt_from_linstr : Spvm.linstr -> int = fun l ->
    let (label,_) = l in
    label
  in*)
  let print_label : Spvm.linstr -> _ = fun b -> 
    let (label,_) = b in
    let _ = print_int label in
    print_string "->" 
  in

  let print_instr : Spvm.linstr -> _ = fun b -> 
    let (_,instr) = b in
    let _ = print_string (Spvm.string_of_instr 0 instr) in
    print_string "\n" 
  in

  let rec remove_element lst target =
    match lst with
    | [] -> []
    | hd :: tl ->
      if hd = target then
        remove_element tl target
      else
        hd :: remove_element tl target
  in

  let rec remove_element2 lst target =
    match lst with
    | [] -> []
    | hd :: tl ->
      let (l, _) = hd in
      if l = target then
        remove_element2 tl target
      else
        hd :: remove_element2 tl target
  in

  let rec init_in_out : int -> int -> in_out list -> in_out list = fun length cur_num answer ->
    if cur_num <= length then 
      init_in_out length (cur_num+1) answer@[(cur_num, ([],[]))]
    else answer
  in
  
  let get_def_from_defuse : def_use -> use = fun def_use ->
    match def_use with
    | (_, du) -> 
      let (def,_) = du in
      def
  in
  let get_use_from_defuse : def_use -> use = fun def_use ->
    match def_use with
    | (_, du) -> 
      let (_,use) = du in
      use
  and get_label_from_defuse : def_use -> int = fun def_use ->
    match def_use with
    | (l,_) -> l
  and get_in_from_oi : oi -> in1 = fun oi ->
    match oi with
    | (_,i) -> i
  in
  let get_out_from_oi : oi -> in1 = fun oi ->
    match oi with
    | (o,_) -> o
  in
  let get_oi_from_outin : in_out -> oi = fun in_out ->
    match in_out with
    | (_, oi) -> oi
  in
  let get_in_from_outin : in_out -> in1 = fun oi ->
    match oi with
    | (_, o) -> get_in_from_oi o
  in
  let get_out_from_outin : in_out -> in1 = fun oi ->
    match oi with
    | (_, o) -> get_out_from_oi o
  in
  let get_dest_from_edge : e1 -> int = fun e ->
    match e with
    | (_,dest) -> dest
  in
  let get_successor : block -> edge -> int list = fun b edge_lst ->
    let get_second_from_edge : e1 -> int = fun e ->
      match e with
      | (start,_) -> start
    in
    let ( block_label, _ ) = b in
    let edges = List.find_all (fun x -> get_second_from_edge x = block_label) edge_lst in
    let edges2 = List.map get_dest_from_edge edges in
    edges2
  and get_successor2 : int -> edge -> int list = fun b_label edge_lst ->
    let edges = List.find_all (fun (start,_) -> start = b_label ) edge_lst in
    let edges2 = List.map get_dest_from_edge edges in
    edges2
  and get_du : def_use -> du = fun defuse ->
    match defuse with
    | (_,du) -> du
  (*and has_successor : block -> edge -> bool = fun b edge_lst ->
    let ( block_label, block_instr_lst ) = b in
    let edges = List.find (fun (start,_) -> start = block_label) edge_lst in
    if List.length edge_lst = 0 then true else false*)
  and get_last_inst : Spvm.program -> Spvm.linstr = fun pgm -> List.hd (List.rev pgm) 
  (*and get_first_from_block : block -> int = fun b -> 
    match b with
    | (block_label, _ ) -> block_label*)
  and get_first_from_block2 : leader_block option -> int = fun b -> 
    match b with
    | None -> raise (Not_Implemented "wrong target!")
    | Some (block_label, _ ) -> block_label
    
  and get_second_from_block : block -> Spvm.program = fun block_lst -> 
    match block_lst with
    | (_, pgm ) -> pgm

  and get_inst_from_spvm : (Spvm.linstr) -> Spvm.instr = fun pgm ->
    match pgm with
    | (_,instr) -> instr
  and get_label_from_spvm : (Spvm.linstr) -> int = fun pgm ->
    match pgm with
    | (l,_) -> l
  and get_block_lst_from_db : def_block -> int list = fun db_block ->
    match db_block with
    | (_, block_lst ) -> block_lst
  (*and get_block_num_from_dcl : dead_code_location -> int = fun dcl->
    match dcl with
    | (block_num,_ ) -> block_num*)
  and get_var_from_db : def_block -> string = fun db_block ->
    match db_block with
    | (var,_ ) -> var

  in
  (* block 분할 , cfg *)
  (*let rec find_leader : Spvm.program -> int list  -> int list = fun pgm answer ->
    match pgm with 
    | [] -> answer
    | (_,Spvm.CJUMP(_,label))::tl -> 
      let (next_label,_) = List.hd tl in
      let new_answer1 = answer@[label] in
      let new_answer2 = new_answer1@[next_label] in
      find_leader tl new_answer2
    | (_,Spvm.UJUMP(label))::tl -> 
      let (next_label,_) = List.hd tl in
      let new_answer = answer@[label]@[next_label] in
      find_leader tl new_answer
    | (_,Spvm.CJUMPF(_,label))::tl -> 
      let (next_label,_) = List.hd tl in
      let new_answer = answer@[label]@[next_label] in
      find_leader tl new_answer
    | _::tl -> find_leader tl answer
  
  *)
  let rec append_inst : Spvm.program -> int -> int -> int list -> Spvm.program -> Spvm.program = fun pgm (leader_num) switch leader_lst answer ->
    match pgm with
    | [] -> answer
    | hd::tl -> 
      let (label,inst) = hd in
      let _ = Spvm.string_of_instr 0 inst in
      if label = leader_num then 
        append_inst tl leader_num 1 leader_lst (answer@[(label,inst)])
      else
        if switch = 1 then 
          if not (List.mem label leader_lst) then append_inst tl leader_num 1 leader_lst (answer@[(label,inst)])
          else answer
        else append_inst tl leader_num 0 leader_lst answer

  and block_partition : Spvm.program -> int list -> int -> block list -> block list  = fun pgm (leader_lst) (block_num) (block_info) -> 
    match leader_lst with
    | [] -> block_info
    | hd::tl -> 
      let block_inst = append_inst pgm hd 0 leader_lst [] in
      (*let _ =  (print_int (List.length block_inst)) in *)
      let new_block_info = (block_num, block_inst) in
      (*let _ = print_string "block number in partition! \n" in*)
      let _ = print_int block_num in
      block_partition pgm tl (block_num + 1) (block_info@[new_block_info])

  and cfg_construction : int -> block list -> (block list) -> edge -> edge = fun b_length b_to_search block_lst answer ->
    match block_lst with
    | [] -> answer
    | hd::tl -> 
      let (block_label, spvm) = hd in
      begin
      if block_label = b_length then
        let (_, instr) = get_last_inst spvm in
        let block_with_leader = List.map (fun (x,s)->(x,List.hd s)) b_to_search in
        begin
        match instr with
        | UJUMP(l) | CJUMP(_,l) | CJUMPF(_,l)-> 
          let _ = print_string "--------------------------jump to where?" in
          let _ = print_instr (get_last_inst spvm) in 
          let target_block = List.find_opt (fun (_, (inst_label,_)) -> inst_label = l) block_with_leader in
          if target_block = None then raise (Not_Implemented "error while finding target block!")
          else
            let target_block_label = get_first_from_block2 target_block in
            cfg_construction b_length b_to_search tl (answer@[(block_label, target_block_label)])
        | _ -> cfg_construction b_length b_to_search tl answer
        end
      else
        let (_, instr) = get_last_inst spvm in
        let new_answer = answer@[(block_label,block_label+1)] in
        let block_with_leader = List.map (fun (x,s)->(x,List.hd s)) b_to_search in

        (*let _ = print_string "----------------------------------------- block with leader! " in*)
        let _ = print_int (List.length block_with_leader) in
        match instr with
        | UJUMP(l) | CJUMP(_,l) | CJUMPF(_,l)-> 
          let _ = print_string "--------------------------jump to where?" in
          let _ = print_instr (get_last_inst spvm) in 
          let target_block = List.find_opt (fun (_, (inst_label,_)) -> inst_label = l) block_with_leader in
          if target_block = None then raise (Not_Implemented "error while finding target block!")
          else
            let target_block_label = get_first_from_block2 target_block in
            cfg_construction b_length b_to_search tl (new_answer@[(block_label, target_block_label)])
        | _ -> cfg_construction b_length b_to_search tl new_answer
        end
  
  (* liveness analysis 구현 *)

  (* def, use 함수 *)
  and find_use : Spvm.instr -> string list = fun i ->
    match i with
    | SKIP -> []
    | FUNC_DEF(_,arg_lst,body) -> 
      let linstr1 = List.map get_second_from_linstr body in
      let linstr2 = List.map find_use linstr1 in
      let linstr3 = List.concat linstr2 in
      let answer = arg_lst in
      answer@linstr3 (* def f(args): body *)
    | CALL(_,f,arg_lst) -> [f]@arg_lst          (* x = call(f, args )*)
    | RETURN(id) -> [id]                           (* return x *) 
    | RANGE(_,lo,hi) -> [lo;hi]                (* x = range(lo, hi) *)
    | LIST_EMPTY(_) -> []               (* x = [] *)
    | LIST_APPEND(lst,elem) -> [lst;elem]              (* append(x,y) *)
    | LIST_INSERT(lst,elem) -> [lst;elem]                  (* insert(x,y) *)
    | LIST_REV(lst) -> [lst]                          (* reverse(x) *)
    | TUPLE_EMPTY(_) -> []                      (* x = () *)
    | TUPLE_INSERT(t,elem) -> [t;elem]                (* tupinsert(x,y) *)
    | ITER_LOAD(_,r1,r_idx) -> [r1;r_idx]               (* x = a[y] *)
    | ITER_STORE(l1,idx,r1) -> [l1;idx;r1]             (* a[x] = y *)
    | ITER_LENGTH(_,r1) -> [r1]                 (* x = len(y) *)
    | ASSIGNV(_,_,r1,r2) -> [r1;r2]          (* x = y bop z *)
    | ASSIGNC(_,_,r1,_) -> [r1]        (* x = y bop n *)
    | ASSIGNU(l1,_,r1) -> [l1;r1]                (* x = uop y *)
    | COPY(_,r1) -> [r1]                          (* x = y *)
    | COPYC(_,_) -> []                      (* x = n *)
    | COPYS(_,_) -> []                 (* x = s *)
    | COPYN(_) -> []                             (* x = None *)
    | UJUMP(_) -> []                          (* goto L *)
    | CJUMP(id,_) ->  [id]                   (* if x goto L *)
    | CJUMPF(id,_) ->  [id]                  (* ifFalse x goto L *)
    | READ(id) -> [id]                             (* read x *)
    | WRITE(id) -> [id]                             (* write x *)
    | INT_OF_STR(_,r1) -> [r1]                   (* x = int(y) *)
    | IS_INSTANCE(_,r1,_) -> [r1]       (* x = isinstance(y, typ) *)
    | ASSERT(id) -> [id]                            (* assert x *)
    | HALT -> []

  and find_def : Spvm.instr -> string list = fun i ->
    match i with
    | SKIP -> []
    | FUNC_DEF(f,_,_) -> [f]  (* def f(args): body *)
    | CALL(l1,_,_) -> [l1]         (* x = call(f, args ) ?*)
    | RETURN(_) -> []                           (* return x *) 
    | RANGE(l1,_,_) -> [l1]                  (* x = range(lo, hi) *)
    | LIST_EMPTY(id) -> [id]               (* x = [] *)
    | LIST_APPEND(lst,_) -> [lst]              (* append(x,y) *)
    | LIST_INSERT(lst,_) -> [lst]                  (* insert(x,y) *)
    | LIST_REV(_) -> []                          (* reverse(x) ? *)
    | TUPLE_EMPTY(t) -> [t]                      (* x = () *)
    | TUPLE_INSERT(t,_) -> [t]                (* tupinsert(x,y) *)
    | ITER_LOAD(l1,_,_) -> [l1]               (* x = a[y] ? *)
    | ITER_STORE(l1,_,_) -> [l1]             (* a[x] = y ?*)
    | ITER_LENGTH(l1,_) -> [l1]                 (* x = len(y) *)
    | ASSIGNV(l1,_,_,_) -> [l1]          (* x = y bop z *)
    | ASSIGNC(l1,_,_,_) -> [l1]        (* x = y bop n *)
    | ASSIGNU(l1,_,_) -> [l1]                (* x = uop y *)
    | COPY(l1,_) -> [l1]                          (* x = y *)
    | COPYC(l1,_) -> [l1]                      (* x = n *)
    | COPYS(l1,_) -> [l1]                 (* x = s *)
    | COPYN(l1) -> [l1]                             (* x = None *)
    | UJUMP(_) -> []                          (* goto L *)
    | CJUMP(_,_) ->  []                   (* if x goto L *)
    | CJUMPF(_,_) ->  []                  (* ifFalse x goto L *)
    | READ(_) -> []                             (* read x *)
    | WRITE(_) -> []                             (* write x *)
    | INT_OF_STR(l1,_) -> [l1]                   (* x = int(y) *)
    | IS_INSTANCE(l1,_,_) -> [l1]       (* x = isinstance(y, typ) *)
    | ASSERT(_) -> []                            (* assert x *)
    | HALT -> []

  

  (************** 1. compute def.use sets *************)
  in
  let rec find_def_use :  block list -> def_use list -> def_use list = fun block_lst def_use_lst -> (*block 리스트에 대해 돌기*)
    (*let rev_block_lst = List.map List.rev block_lst in*)
    (*let end_of_blocks  = List.map List.hd rev_block_lst in*)
    let rec help_find_def_use : Spvm.program -> du ->  du = fun spvm_lst answer -> (* block 안의 instruction에 대해 돌기 *)
      let use_answer, def_answer = answer in
      let instr_lst = List.map get_inst_from_spvm (spvm_lst) in

      (*let _ = print_string "&&&&&&&&&&" in*)
      (*let _ = print_int (List.length instr_lst )in*)
      begin
      match instr_lst with 
      | [] -> answer
      | hd::_ -> 
        let new_use_set = find_use hd in
        
        let new_def_set = find_def hd in
        
        let new_use_answer = BatSet.union (BatSet.of_list use_answer) (BatSet.of_list new_use_set) in
        let new_def_answer = BatSet.union (BatSet.of_list def_answer) (BatSet.of_list new_def_set) in
        help_find_def_use (List.tl spvm_lst) (BatSet.to_list new_def_answer, BatSet.to_list new_use_answer)
      end
    in
    match block_lst with
    | [] -> def_use_lst
    | hd::tl -> 
      let ( block_label, instr_lst ) = hd in
      let block_du = help_find_def_use instr_lst ([],[]) in

      let new_du_lst = def_use_lst@[(block_label, block_du)] in
      find_def_use tl new_du_lst 
      (* 마지막 block은 out 계산 시 조금 다르게*)    
    (*and help_last_block : block -> duoi -> duoi = fun last_block ->
      let (_,pgm) = last_block in
      let instr_lst = List.map (get_inst_from_spvm pgm) in (*각 block들 리스트에서 마지막 block만 추출*)
      let out_lst = [] in*)
  (************** 2. compute in.out sets *************)
  and iterate_find_out_in : block list -> edge -> in_out list -> def_use list -> in_out list = fun b e o d ->
    let rec find_out_in : block list -> edge -> in_out list -> def_use list -> in_out list = fun block_lst edge_lst out_in_lst def_use_lst ->
      (*let rev_block_lst = List.rev block_lst in*)
      match block_lst with
      | [] -> out_in_lst
      | hd::tl -> 
        let ( block_label, _) = hd in
        (*해당 블럭의 (def,use) 가져오기 *)
        let def_use = List.find (fun ( l , (_,_)) -> l = block_label) def_use_lst in
        let def_use2 = get_du def_use in
        (* in/out 계산 *)
        let old_in_out = List.find (fun ( l , (_,_)) -> l = block_label) out_in_lst in
        
        let oii = get_oi_from_outin old_in_out in
        let out_answer, in1_answer = oii in
        let def_set, use_set = def_use2 in

        let succ_lst = get_successor (*hd*) hd edge_lst in
        let succ_lst2 = List.map (fun x -> (List.find (fun (y,_) -> y=x) out_in_lst) ) succ_lst in 
        
        let succ_in_lst0 = List.map ( fun (_,oi) -> oi ) succ_lst2 in
        let succ_in_lst = List.map (fun (_,i) -> i ) succ_in_lst0 in 
        
        (*let _ = List.map (fun y -> List.iter (fun x -> print_string "succ list for new out set!" ; print_string x ; print_string " "; print_string "\n") y) succ_in_lst in*)
      
        
    (* out, in set 계산 *)
        let new_out_set = List.concat succ_in_lst in
        let new_in_set =  BatSet.union (BatSet.of_list use_set) (BatSet.diff (BatSet.of_list new_out_set) (BatSet.of_list def_set)) in
    
    (* old answer와 합집합 *)
        let new_in_answer = BatSet.union (BatSet.of_list in1_answer) (new_in_set) in
        let new_out_answer = BatSet.union (BatSet.of_list out_answer) (BatSet.of_list new_out_set) in

        let new_answer = (BatSet.to_list new_out_answer, BatSet.to_list new_in_answer) in
        let new_element_for_lst = (block_label, new_answer) in
        let target = List.find (fun (x,_) -> x = block_label ) out_in_lst in
        let removed_answer = remove_element out_in_lst target in
        find_out_in tl edge_lst (removed_answer@[new_element_for_lst]) def_use_lst
            (*help_find_out_in (List.tl spvm_lst) edge_lst new_answer def_use*)
        (*let block_io = help_find_out_in (*instr_lst*) hd edge_lst ([],[]) def_use2 in
        let new_io_lst = out_in_lst::(block_label, block_io) in
        new_io_lst*)
    in
    let new_answer = find_out_in (List.rev b) e o d in
    let diff = (BatSet.compare (BatSet.of_list new_answer) (BatSet.of_list o)) in
    begin
    match diff with
    | 0 -> new_answer
    | _ -> find_out_in b e new_answer d 
    end
  
  (********* 3. check the dead code **********)
  and find_def_block_for_var : def_use list -> string -> int list -> int list = fun (du_lst) (var_to_find) answer->
    match du_lst with
    | [] -> answer
    | hd::tl ->
      let def_lst = get_def_from_defuse hd in

      (*let _ = print_string("var to find all defined blocks!"^"\n" ) in
      let _ = print_string (var_to_find ^ "\n" ) in*)

      (*let _ = print_string("current block's def list!"^"\n" ) in*)
      (*let _ = List.iter (fun x -> print_string x) def_lst in*)
      (*let _ = print_string ( "\n" ) in*)

      if List.mem var_to_find def_lst then
        (*let _ = print_string ( "true!\n" ) in*)
        let block_num = get_label_from_defuse hd in
        find_def_block_for_var tl var_to_find (answer@[block_num])
      else find_def_block_for_var tl var_to_find answer
  
  and find_def_block_per_var : string list -> def_use list -> def_block list -> def_block list = fun var_lst du_lst answer ->
    match var_lst with
    | [] -> answer
    | hd::tl -> 
      let def_lst = find_def_block_for_var du_lst hd [] in
      (*
      let _ = List.iter (fun x -> print_int x; print_string " ") def_lst in*)
      find_def_block_per_var tl du_lst answer@[(hd,def_lst)]
  
  and find_all_defined_var : def_use list -> string list -> string list = fun (du_lst) answer ->
    match du_lst with
    | [] -> answer
    | hd::tl ->
      let def_lst = get_def_from_defuse hd in
      let new_answer = BatSet.union (BatSet.of_list answer) (BatSet.of_list def_lst) in
      find_all_defined_var tl (BatSet.to_list new_answer)

  and reachable_node_per_def : int -> int list -> edge -> int list = fun (start_block_num) (other_blocks) (edge_lst) ->
    let rec help_reachable_node : int list -> int list -> int list -> edge -> int list -> int list = fun (to_visit_lst) (other_blocks) (visited_lst) (edge_lst) answer ->
      match to_visit_lst with
      | [] -> answer
      | hd::tl -> 

        (*let _ = print_string("other defined blocks list "^"\n" ) in
        let _ = List.iter (fun x -> print_int x ; print_string " ") (other_blocks) in*)

        if List.mem hd other_blocks then (*answer*)
          let new_visited_lst = visited_lst@[hd] in

          let new_succ_lst = get_successor2 hd edge_lst in
          (*let _ = print_string("successor2 list "^"\n" ) in
          let _ = List.iter (fun x -> print_int x ; print_string " ") (new_succ_lst) in*)

          (*let added_succ_lst = BatSet.union (BatSet.of_list new_succ_lst) (BatSet.of_list answer) in*)
          (*let new_answer = BatSet.to_list added_succ_lst in*)
          let new_answer = answer@[hd] in

          let never_visited_lst = BatSet.to_list (BatSet.diff (BatSet.of_list new_succ_lst) (BatSet.of_list visited_lst) ) in
          let new_to_visit_lst = tl@never_visited_lst in

          
          help_reachable_node new_to_visit_lst other_blocks new_visited_lst edge_lst new_answer
        else
          let new_visited_lst = visited_lst@[hd] in

          let new_succ_lst = get_successor2 hd edge_lst in
          (*let _ = print_string("successor2 list "^"\n" ) in
          let _ = List.iter (fun x -> print_int x ; print_string " ") (new_succ_lst) in*)

          (*let added_succ_lst = BatSet.union (BatSet.of_list new_succ_lst) (BatSet.of_list answer) in*)
          (*let new_answer = BatSet.to_list added_succ_lst in*)
          let new_answer = answer@[hd] in

          let never_visited_lst = BatSet.to_list (BatSet.diff (BatSet.of_list new_succ_lst) (BatSet.of_list visited_lst) ) in
          let new_to_visit_lst = tl@never_visited_lst in

          
          help_reachable_node new_to_visit_lst other_blocks new_visited_lst edge_lst new_answer
    in
    let result = help_reachable_node [start_block_num] other_blocks [] edge_lst [] in
    (*let _ = print_string("result list"^"\n" ) in
    let _ = List.iter (fun x -> print_int x ; print_string " ") (result) in*)
    let result1 = remove_element result start_block_num in
    (*let _ = print_string("result list"^"\n" ) in
    let _ = List.iter (fun x -> print_int x ; print_string " ") (result1) in*)
    result1

  and dead_code :  block list -> def_use list -> in_out list -> edge -> int list = fun (block_lst) (def_use_lst) (in_out_lst) (edge_lst) ->
    let rec check_dead_per_inst : block list -> dead_code_location list -> int list -> int list = fun block_lst dead_code_lst answer ->
      let rec instr_to_erase : Spvm.program -> string -> int list -> int list = fun instr_lst var answer ->
        match instr_lst with
        | [] -> answer
        | hd::tl -> 
          let instr_to_check = get_inst_from_spvm hd in
          let instr_num = get_label_from_spvm hd in
          let defined_var_lst = find_def instr_to_check in
          if List.length (defined_var_lst) = 0 then instr_to_erase tl var answer
          else if List.hd (defined_var_lst) = var then 
            let new_answer = answer@[instr_num] in
            instr_to_erase tl var new_answer
          else instr_to_erase tl var answer
      in
      match dead_code_lst with
      | [] -> answer
      | hd::tl ->
        let block_num, var = hd in
        let block_to_search = List.find (fun (l,_) -> l = block_num) block_lst in
        let instr_lst = get_second_from_block block_to_search in
        let instr_to_erase_lst = instr_to_erase instr_lst var [] in
        let new_answer = answer@instr_to_erase_lst in
        check_dead_per_inst (block_lst) tl (new_answer)
                  
    and help_check_dead_code : (def_block list) -> edge -> in_out list -> dead_code_location list -> dead_code_location list = fun db_lst edge_lst oi_lst answer ->
      let rec help_find_reachable : int list -> string -> edge -> in_out list -> dead_code_location list -> dead_code_location list = fun block_lst var edge_lst oi_lst answer ->
        let rec check_in_has_val : string -> in_out list -> int list -> bool = fun var (oi_lst) (reachable_nodes) ->
          match reachable_nodes with
          | [] -> true
          | hd::tl ->
            let oi_lst_for_r = get_oi_from_outin (List.find (fun (l,_) -> l = hd ) oi_lst) in
            let in_lst = get_in_from_oi (oi_lst_for_r) in

            (*let _ = print_string("in list! in the dead code func" ) in
            let _ = List.iter (fun x -> print_string x ; print_string " ") (in_lst) in
            let _ = print_string ("var to check if it's dead "^var^"\n") in*)

            if List.mem var in_lst then false
            else check_in_has_val var (oi_lst) tl
        in
        match block_lst with
        | [] -> answer
        | hd::tl ->
          let reachable_nodes0 = reachable_node_per_def hd tl edge_lst in

          let reachable_nodes = remove_element reachable_nodes0 hd in

          (*let _ = print_string("reachable nodes list"^"\n" ) in
          let _ = List.iter (fun x -> print_int x ; print_string " ") (reachable_nodes) in*)

          if (check_in_has_val (var) (oi_lst) (reachable_nodes)) then
            let new_dead_code = (hd,var) in
            let new_answer = answer@[new_dead_code] in
            help_find_reachable tl var edge_lst oi_lst new_answer
          else help_find_reachable tl var edge_lst oi_lst answer
      in
      match db_lst with
      | [] -> answer
      | hd::tl ->
        let block_lst = get_block_lst_from_db hd in
        let var = get_var_from_db hd in        
        let new_answer = help_find_reachable block_lst var edge_lst oi_lst [] in

        (*let _ = print_string("defined blocks list "^"\n" ) in*)
        let _ = List.iter (fun x -> print_int x ; print_string " ") (block_lst) in

        help_check_dead_code tl (edge_lst) (oi_lst) (answer@new_answer)
    in
    let all_var = find_all_defined_var def_use_lst [] in

    let _ = print_string("all variables defined!-----------"^"\n" ) in
    let _ = List.iter (fun x -> print_string x; print_string " ") all_var in

    let def_block_per_var = (find_def_block_per_var) all_var def_use_lst [] in

    let dead_code_lst = help_check_dead_code (def_block_per_var) (edge_lst) (in_out_lst) [] in

    (*let _ = List.iter (fun x -> print_int x ; print_string " ") (get_block_num_from_dcl (List.hd dead_code_lst)) in*)
    check_dead_per_inst (block_lst) (dead_code_lst) []      
  (*********function ended**********)
  in
  (*let (first_label, _) = List.hd pgm in*)
  (*let leader_lst0 = find_leader pgm [first_label] in*)
  let leader_lst = List.map (fun (x,_) -> x) pgm in
  (*let leader_lst = List.sort (fun x y -> x - y) leader_lst0 in*)
  (*let _ = List.iter (fun x -> print_int x ; print_string " "; print_string "\n") leader_lst in*)
  let block_lst = block_partition pgm leader_lst 1 [] in

  let _ = List.iter ( fun y -> (List.iter (fun x -> print_label x; print_instr x) ) y ) (List.map get_second_from_block block_lst) in

  let _ = print_string "instr label-------------------!\n" in
  let _ = List.iter (fun (b_label,y) -> ( print_int b_label; (List.iter (fun (label,_) -> print_int label; print_string " ") y) ) ) block_lst in
  
  let _ = print_string "block length!" in
  let _ = print_int (List.length block_lst) in
  let _ = print_string "\n" in

  let edge_lst = cfg_construction (List.length block_lst) block_lst block_lst [] in
  let _ = print_string "edge list length!" in
  let _ = print_int (List.length edge_lst) in
  let _ = print_string "\n" in
  (*let cfg = (block_lst, edge_lst) in*) 

  let def_use_lst = find_def_use block_lst [] in
  let def1 = List.map get_def_from_defuse def_use_lst in
  let use1 = List.map get_use_from_defuse (def_use_lst) in
  let _ = print_string "---------------------------def list!!!!!!" in
  let _ = print_string "\n" in
  let _ = List.map (fun y -> List.iter (fun x -> (print_string x ; print_string " ")) y) def1 in
  let _ = print_string "---------------------------use list!!!!!!" in
  let _ = List.map (fun y -> List.iter (fun x -> ((*if x = ".t1" then*) print_string x ; print_string " ")) y) use1 in

  let initialized_in_out_lst = init_in_out (List.length block_lst) 1 [] in
  let _ = print_string "---------------------------initialized list!!!!!!" in
  let _ = print_int (List.length initialized_in_out_lst) in 
  let in_out_lst = iterate_find_out_in block_lst edge_lst initialized_in_out_lst def_use_lst in 
  let in1 = List.map get_in_from_outin (in_out_lst) in
  let out1 = List.map get_out_from_outin (in_out_lst) in

  let _ = print_string "----------------------------out list!!!!!!" in
  let _ = print_string "\n" in
  let _ = List.map (fun y -> List.iter (fun x -> (print_string x ; print_string " ")) y; print_string ",";) out1 in
  let _ = print_string "-------------------------in list!!!!!! \n" in
  let _ = List.map (fun y -> List.iter (fun x -> (if x = ".t4" then print_string x ; print_string " ")) y) in1 in

  let instr_to_erase = dead_code block_lst def_use_lst in_out_lst edge_lst in
  let _ = print_string "-------------------------dead code here! \n" in
  let _ = List.iter (fun x -> print_int x ; print_string " ") instr_to_erase in
  let rec remove_spvms : Spvm.program -> int list -> Spvm.program  = fun pgm1 instr_to_erase  ->
    match instr_to_erase with
    | [] -> pgm1
    | hd::tl -> 
      let new_pgm = (remove_element2 pgm1 hd) in
      remove_spvms new_pgm tl 
  in
  
  (*let get_second_from_copys : Spvm.instr -> string = fun instr ->
    match instr with
    | COPYS(_,s) -> s
    | _ -> raise (Not_Implemented "not copys!")
  in*)
(*
  let get_var_from_writes : Spvm.instr -> string = fun instr ->
    match instr with
    | WRITE(id) -> id
    | _ -> raise (Not_Implemented "not writes!")
  in

  let check_if_enter : Spvm.linstr -> bool = fun linstr ->
    let x = get_inst_from_spvm linstr in
    match x with
    | COPYS(_,s) -> 
      if s = "\n" then true
      else false
    | _ -> false
  in

  let rec return_next_element : Spvm.program -> Spvm.program -> Spvm.program = fun check answer ->   
    match check with
    | [] -> answer
    | hd::tl ->
      if check_if_enter hd then return_next_element tl answer@[(get_label_from_spvm (List.hd tl), get_inst_from_spvm (List.hd tl))]
      else return_next_element tl answer

  in

  let n1 = List.map ( fun x -> (if (check_if_enter x) then (get_label_from_spvm x) else -1 )  ) pgm in

  let _ = print_string "------------------- enter int list" in  

  let n2 = remove_element n1 (-1) in
  let _ = List.iter (fun x -> print_int x; print_string " " ) n2 in
  let n3 = return_next_element pgm [] in 
  let n4 = n1 @ List.map get_label_from_spvm n3 in 
  let n5 = List.map get_label_from_spvm (List.rev (return_next_element (List.rev pgm) [])) in 

  let _ = print_string "------------------- enter previous list" in 
  let _ = List.iter (fun x -> print_int x; print_string " " ) n5 in

  let rec find_above_enter0 : Spvm.program -> Spvm.program -> int list -> Spvm.program -> Spvm.program = fun opgm pgm change_lst answer ->
    let rec find_above_enter : Spvm.program -> Spvm.program -> int -> Spvm.program -> Spvm.program = fun opgm pgm label_to_change answer ->
      let rec change_instr : string -> Spvm.program -> Spvm.program -> Spvm.program = fun var l answer ->
        let help_change_instr : string -> Spvm.linstr -> Spvm.linstr = fun var linst ->
          let inst = get_second_from_linstr linst in
          let label = get_fisrt_from_linstr linst in
          match inst with
          | COPY(x,y) -> 
            if x = var then 
              let new_answer = y^"\n" in
              (label, COPY(x,new_answer))
            else linst
          | COPYC(x,n) -> 
            if x = var then 
              let new_answer = (string_of_int n)^"\n" in
              (label, COPY(x,new_answer))
            else linst
          | COPYN(x) -> 
            if x = var then (label,COPYS(x,"\n"))
            else linst
          | _ -> linst
        in
        match l with
        | [] -> answer
        | hd::tl -> change_instr var tl (answer@[help_change_instr var hd])
      in
      match pgm with
      | [] -> answer
      | hd::tl ->
        let label1 = get_label_from_spvm hd in
        if label1 = label_to_change then 
          let a1 = get_inst_from_spvm hd in 
          match a1 with
          | WRITE(_) ->
            let _ = print_string "------------------- enter write!" in  
            let id = (get_var_from_writes a1) in
            let _ = print_string id in
            let new_answer = change_instr id opgm [] in
            find_above_enter opgm tl label_to_change new_answer
          | _ -> find_above_enter opgm tl label_to_change answer
        else find_above_enter opgm tl label_to_change answer
    in
    let _ = print_string "------------------- enter change list" in  
    let _ = List.iter (fun x -> print_int x; print_string " " ) change_lst in
    match change_lst with
    | [] -> answer
    | hd::tl -> 
      let new_answer = find_above_enter opgm pgm hd answer in
      find_above_enter0 opgm pgm tl new_answer 
  in    
  let modified_spvm_lst = find_above_enter0 pgm pgm n5 [] in
  let new_instr_to_erase = BatSet.union (BatSet.of_list instr_to_erase) (BatSet.of_list n4) in*)
  let filtered_spvm_lst = remove_spvms (*(modified_spvm_lst)*) pgm instr_to_erase (*(BatSet.to_list new_instr_to_erase)*) in
  (*let filtered_spvm_lst = (List.map ( fun y -> List.filter (fun (x,_) -> x = y ) pgm ) instr_to_erase) in*)

  
  filtered_spvm_lst