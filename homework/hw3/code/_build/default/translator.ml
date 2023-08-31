
open Spy
open Lib.Util
open Spvm


let temp_var_index = ref 0
let label_index = ref 1
let new_temp_var() = temp_var_index := !temp_var_index + 1; ".t" ^ (string_of_int !temp_var_index)
let new_label() = label_index := !label_index + 1; !label_index

exception Not_Implemented of string 
exception Error of string (* raise when syntax is beyond Spy *)

let translate : Spy.program -> Spvm.program = fun spyPgm -> 
    let sidx = ref 0 in
    let labelx = ref 0 in
    let new_state() = sidx := !sidx + 1; !sidx in
    let new_label() = labelx := !labelx + 1; !labelx in

    let rec unpack_all : expr list -> expr list = fun group ->
      let rec help_unpack_all : expr -> expr list = fun e ->
        match e with
        | Spy.List(expr_lst) | Spy.Tuple(expr_lst) ->
          begin match expr_lst with
          | [hd] -> [hd]
          | hd::tl -> (help_unpack_all hd) @ (help_unpack_all (Spy.List(tl)))
          | [] -> []
          end
        | _ as other -> [other]
        in
      match group with
        | [] -> []
        | hd::tl -> (help_unpack_all hd)@(unpack_all tl)
      (*| [] -> []
      | (hd,tl)::tl' -> (unpack_all [hd;tl]) @ (unpack_all tl')
      | hd::tl -> hd :: unpack_all tl
      | _ -> []*)

    in

    let assign_fun : (string option*string option) -> stmt = fun var -> 
      let exp1, exp2 = var in 
      match exp1 with
      | Some e -> 
        begin
        match exp2 with
        | Some e2 -> 
          let _ = prerr_endline("here again!") in
          Spy.Assign([Name(e)],Name(e2))
        | None -> Spy.Assign([Name(e)],Constant(CNone))
        end
      | None ->
        match exp2 with
        | Some e2 -> Spy.Assign([],Name(e2))
        | None -> Spy.Assign([],Constant(CNone))
      
    
    in

    (*let assign_elem : expr -> Spvm.program = fun elem ->
      let new_answer_lst = help_translate [expr] [] 0 in
      let is = new_state () in
      new_answer_lst@[(new_label(),COPY("t"^(string_of_int is),elem))]

    in

    let write_elem : expr -> Spvm.pgm = fun elem ->
      let new_answer0 = assign_elem expr in
      let assigned_var0 = get_last_elem new_answer0 in
      let assigned_var1 = get_idt_from_copy assigned_var0 in
      new_answer0@[(new_label(),WRITE(assigned_var1))]

    in*)
    let string_instr : Spvm.instr -> string = fun instr ->
      match instr with
      | HALT -> "HALT"
      | SKIP -> "SKIP"
      | FUNC_DEF (f, args, _) -> 
        ("def " ^ f ^ string_of_list ~sep:", " id args)
      | RETURN x -> "return " ^ x
      | COPYN x -> x ^ " = None"
      | CALL (x, f, args) -> x ^ " := call(" ^ f ^ ", " ^ string_of_list id args ^ ")"
      | ASSIGNV (x,o,y,z) -> x ^ " = " ^ y ^ " " ^ string_of_bop o ^ " " ^ z
      | ASSIGNC (x,o,y,n) -> x ^ " = " ^ y ^ " " ^ string_of_bop o ^ " " ^ string_of_int n
      | ASSIGNU (x,o,y) -> x ^ " = " ^ string_of_uop o ^ y
      | COPY (x,y) -> x ^ " = " ^ y
      | COPYC (x,n) -> x ^ " = " ^ string_of_int n
      | COPYS (x,s) -> x ^ " = " ^ "\"" ^ String.escaped s ^ "\""
      | UJUMP label -> "goto " ^ string_of_int label
      | CJUMP (x,l) -> "if " ^ x ^ " goto " ^ string_of_int l
      | CJUMPF (x,l) -> "iffalse " ^ x ^ " goto " ^ string_of_int l
      | READ x -> "read " ^ x
      | RANGE (x, y, z) -> x ^ " = " ^ " range(" ^ y ^ ", " ^ z ^ ")"
      | LIST_EMPTY x -> x ^ " = []"
      | LIST_APPEND (x,y) -> x ^ " = " ^ x ^ "@[" ^ y ^ "]"
      | LIST_INSERT (x,y) -> x ^ " = " ^ y ^ "::" ^ x ^ ""
      | TUPLE_EMPTY x -> x ^ " = ()"
      | TUPLE_INSERT (x,y) -> x ^ " = (" ^ y ^ ") + " ^ x
      | ITER_LOAD (x,l,y) -> x ^ " = " ^ l ^ "[" ^ y ^ "]"
      | ITER_STORE (l,x,y) -> l ^ "[" ^ x ^ "] = " ^ y
      | LIST_REV x -> "LIST_REV " ^ x
      | ITER_LENGTH (x,y) -> x ^ " = len(" ^ y ^ ")"
      | INT_OF_STR (x,y) -> x ^ " = int(" ^ y ^ ")"
      | ASSERT x -> "assert " ^ x
      | IS_INSTANCE (x, y, typ) -> x ^ " = isinstance(" ^ y ^ ", " ^ typ ^ ")"
      | WRITE x -> "write " ^ x
    in

    let get_string_from_idt : Spy.expr -> string = fun name ->
      match name with
      | Name(idt) -> idt
      | _ -> ""
    in 

    let get_constant_from_expr : Spy.stmt -> int = fun cst ->
      match cst with
      | Expr(Constant(CInt(i1))) -> i1
      | _ -> raise (Not_Implemented "not constant")

    in

    let get_idt_from_copy : Spvm.linstr -> string = fun instr1  ->
      let (_,cpy_instr) = instr1 in
      match cpy_instr with
      | INT_OF_STR(v1,_) -> v1
      | READ(v1) -> v1
      | ASSIGNV(v1,_,_,_) -> v1
      | ASSIGNC(v1,_,_,_) -> v1
      | ASSIGNU(v1,_,_) -> v1
      | CALL(v1,_,_) -> v1
      | COPY(v1,_) -> v1
      | COPYC(v1,_) -> v1
      | COPYS(v1,_) -> v1
      | COPYN(v1) -> v1
      | ITER_LOAD(v1,_,_) -> v1
      | _ -> 
        let str1 = string_instr cpy_instr in
        let _ = prerr_endline (str1) in
        raise (Not_Implemented "can't get idt from copy")
    
    in

    let print_instr_from_linstr : Spvm.linstr -> unit = fun instr1 ->
      let (_,cpy_instr) = instr1 in
      let str1 = string_instr cpy_instr in
      prerr_endline (str1)

    in

    let get_var_from_assign : Spvm.linstr -> string = fun instr1 ->
        let (_,assign_instr) = instr1 in
        let str1 = string_instr assign_instr in
        let _ = prerr_endline (str1) in
        match assign_instr with
        | INT_OF_STR(v1,_) -> v1
        | READ(v1) -> v1
        | ASSIGNV(v1,_,_,_) -> v1
        | ASSIGNC(v1,_,_,_) -> v1
        | ASSIGNU(v1,_,_) -> v1
        | CALL(v1,_,_) -> v1
        | COPY(v1,_) -> v1
        | COPYC(v1,_) -> v1
        | COPYS(v1,_) -> v1
        | COPYN(v1) -> v1
        | ITER_LOAD(v1,_,_) -> v1
        | _ -> 
          let str1 = string_instr assign_instr in
          let _ = prerr_endline (str1) in
          raise (Not_Implemented "can't get idt from copy") 


    in

    (*let insert_at x n lst =
      let rec insert_at_helper acc n = function
      | [] -> List.rev (x::acc)
      | hd::tl as l ->
        if n = 0 then List.rev_append acc (x::l)
        else insert_at_helper (hd::acc) (n-1) tl
      in
    insert_at_helper [] n lst*)

    let rec insert_after : stmt list -> Spy.stmt -> Spy.stmt -> stmt list = fun lst target item ->
      match lst with
      | [] -> []
      | hd::tl ->
        if hd = target then
          hd :: item :: (insert_after tl target item)
        else
          match hd with
          | If(expr,stmt0,stmt1) -> 
            let new_stmt0 = insert_after stmt0 target item in
            let new_stmt1 = insert_after stmt1 target item in
            let new_hd = If(expr,new_stmt0,new_stmt1) in
            new_hd :: insert_after tl target item
          (*| Expr(IfExp(expr0,expr1,expr2)) ->
            let new_expr1 = insert_after Expr(expr1) target item in
            let new_expr2 = insert_after Expr(expr2) target item in
            let new_ifexp = IfExp(expr0,new_expr1,new_expr2) in
            let new_hd = Expr(new_ifexp) in
            new_hd :: insert_after tl target item*)
          | _ -> hd :: insert_after tl target item
    in

    let rec drop_last : 'a list -> 'a list = fun lst ->
      match lst with
      | [] -> failwith "empty list"
      | [_] -> []
      | hd::tl -> hd :: drop_last tl

    in

    let get_last_elem : 'a list -> 'a = fun lst -> List.hd (list_rev lst)

    in

    let get_from_return : Spvm.linstr -> string = fun instr1 -> 
      let (_,assign_instr) = instr1 in
      match assign_instr with
      | RETURN(id) -> id
      | _ -> raise (Not_Implemented "can't get from SPVM return, it's not return") 
    
    in

    let get_from_name : Spy.expr -> string = fun expr0 ->
      match expr0 with
      | Name(id) -> id
      | _ -> raise (Not_Implemented "can't get from Spy name, it's not name") 

    in
    
    let get_string_from_constant : Spy.expr -> string = fun expr0 ->
      match expr0 with 
      | Constant(cst) -> 
        begin
        match cst with
        | CString(s) -> s
        | _ -> raise (Not_Implemented "not string") 
        end
      | _ -> raise (Not_Implemented "not constant") 

    in

    (*let rec test_boolopr : Spy.boolop -> expr list -> Spvm.program = fun booloper expr_lst -> 
      match expr_lst with
      | hd::tl ->
        let l_len = List.length expr_lst in
        if l_len > 2 then
          let answer0 = help_translate [Expr(hd)] [] 0 in
          let hd_var = get_var_from_assign (get_last_elem new_answer0) in
          let new_answer1 = new_answer0@(test_boolopr booloper tl) in
          let tl_var = get_var_from_assign (get_last_elem new_answer1) in
          let new_var = "t"^new_state() in
          match booloper with
          | And ->
            let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,AND,hd_var,tl_var))] in
            new_answer2
          | Or -> 
            let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,OR,hd_var,tl_var))] in
            new_answer2
        else if l_len = 2 then 
          let answer0 = help_translate [Expr(hd)] [] 0 in
          let hd_var = get_var_from_assign (get_last_elem new_answer0) in
          let new_answer1 = new_answer0@(hlep_translate [Expr(tl)] [] 0) in
          let tl_var = get_var_from_assign (get_last_elem new_answer1) in
          let new_var = "t"^new_state() in
          match booloper with
          | And ->
            let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,AND,hd_var,tl_var))] in
            new_answer2
          | Or ->
            let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,OR,hd_var,tl_var))] in
            new_answer2  
        else raise (Not_Implemented "error grouping multiple boolopr")  
      | [] -> raise (Not_Implemented "error grouping") 

    in*)

    let rec help_translate : Spy.program -> Spvm.program -> int -> Spvm.program = fun pgm answer switch ->
      (*let (label,_) = if List.is_empty answer then 1 else List.hd answer in*)
      let assign_elem : Spy.expr -> Spvm.program = fun elem ->
        let new_answer_lst = help_translate [Expr(elem)] [] 0 in
        let new_answer0 = get_last_elem new_answer_lst in 
        let new_var = get_var_from_assign new_answer0 in
        let is = new_state () in
        new_answer_lst@[(new_label(),COPY("t"^(string_of_int is),new_var))]
  
      in
  
      let write_elem : Spy.expr -> Spvm.program = fun elem ->
        let new_answer0 = assign_elem elem in
        let assigned_var0 = get_last_elem new_answer0 in
        let assigned_var1 = get_idt_from_copy assigned_var0 in
        let enter_state_var = "t"^(string_of_int (new_state())) in
        let assigned_enter = [(new_label(),COPYS(enter_state_var,"\n"))] in
        new_answer0@[(new_label(),WRITE(assigned_var1))]@assigned_enter@[(new_label(),WRITE(enter_state_var))]
      in

      let rec test_boolopr : Spy.boolop -> expr list -> Spvm.program = fun booloper expr_lst -> 
        match expr_lst with
        | hd::tl ->
          let l_len = List.length expr_lst in
          if l_len > 2 then
            let new_answer0 = help_translate [Expr(hd)] [] 0 in
            let hd_var = get_var_from_assign (get_last_elem new_answer0) in
            let new_answer1 = new_answer0@(test_boolopr booloper tl) in
            let tl_var = get_var_from_assign (get_last_elem new_answer1) in
            let new_var = "t"^(string_of_int (new_state())) in
            match booloper with
            | And ->
              let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,AND,hd_var,tl_var))] in
              new_answer2
            | Or -> 
              let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,OR,hd_var,tl_var))] in
              new_answer2
          else if l_len = 2 then 
            let new_answer0 = help_translate [Expr(hd)] [] 0 in
            let hd_var = get_var_from_assign (get_last_elem new_answer0) in
            let new_answer1 = new_answer0@(help_translate [Expr(List.hd tl)] [] 0) in
            let tl_var = get_var_from_assign (get_last_elem new_answer1) in
            let new_var = "t"^(string_of_int (new_state())) in
            match booloper with
            | And ->
              let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,AND,hd_var,tl_var))] in
              new_answer2
            | Or ->
              let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var,OR,hd_var,tl_var))] in
              new_answer2  
          else raise (Not_Implemented "error grouping multiple boolopr")  
        | [] -> raise (Not_Implemented "error grouping") 
      in

        match pgm with
        | [] -> answer
        | Spy.Expr(expr)::tl ->
          begin
          match expr with
          | Spy.ListComp(_,_) -> raise (Not_Implemented "listcomp not implemented") 
          | Spy.Attribute(expr,_) -> 
            begin
            match expr with
            | Name(idf) -> 
              let new_var = "t"^(string_of_int (new_state())) in
              help_translate tl (answer@[(new_label(),COPY(new_var, idf))]) 0
            | _ -> raise (Not_Implemented "another object for attribute not implemented")
            end
          | Spy.Subscript(expr01,expr02) ->
            begin
            match expr01 with
            | Name(idf) -> 
              let new_answer0 = answer@(help_translate [Expr(expr02)] [] 0) in
              let index_var = get_idt_from_copy (get_last_elem new_answer0) in
              let new_var = "t"^(string_of_int (new_state())) in
              let new_answer1 = new_answer0@[(new_label(),ITER_LOAD(new_var,idf,index_var))] in
              help_translate tl new_answer1 0
            | _ ->
              let new_answer0 = answer@(help_translate [Expr(expr02)] [] 0) in
              let index_var = get_idt_from_copy (get_last_elem new_answer0) in
              let new_answer1 = new_answer0@(help_translate [Expr(expr01)] [] 0) in
              let iter_var = get_idt_from_copy (get_last_elem new_answer1) in
              let new_var = "t"^(string_of_int (new_state())) in
              let new_answer2 = new_answer1@[(new_label(),ITER_LOAD(new_var,iter_var,index_var))] in
              help_translate tl new_answer2 0
            end
          | Spy.Name(idfe) ->
            let _ = prerr_endline("name : "^idfe) in
            let is = new_state () in
            let new_var = "t"^(string_of_int is) in
            let new_answer0 = answer@[(new_label(), COPY(new_var, idfe))] in
            help_translate tl new_answer0 0
          | Spy.Constant(cst) -> 
            let is = new_state () in
            let new_var = "t"^(string_of_int is) in
              begin
              match cst with
              | CInt(i1) -> 
                let new_answer = answer@[(new_label(), COPYC(new_var, i1))] in
                (*let new_answer0 = new_answer@[(new_label(), COPY(idt,new_var))] in*)
                help_translate tl new_answer 0
              | CString(s1) -> 
                let new_answer = answer@[(new_label(), COPYS(new_var, s1))] in
                (*let new_answer0 = new_answer@[(new_label(), COPY(idt,new_var))] in*)
                help_translate tl new_answer 0
              | CBool(b1) -> 
                if b1 = true then let new_answer = answer@[(new_label(), COPYC(new_var, 1))] in
                (*let new_answer0 = new_answer@[(new_label(), COPY(idt,new_var))] in*)
                help_translate tl new_answer 0
                else let new_answer = answer@[(new_label(), COPYC(new_var, 0))] in
                (*let new_answer0 = new_answer@[(new_label(), COPY(idt,new_var))] in*)
                help_translate tl new_answer 0
              | CNone -> 
                let new_answer = answer@[(new_label(), COPYN(new_var))] in
                (*let new_answer0 = new_answer@[new_label(), COPY(idt,new_var)] in*)
                help_translate tl new_answer 0
              end
          | Spy.List(expr_lst) ->
            let new_answer0 = List.map assign_elem expr_lst in
            let assigned_lst0 = List.map get_last_elem new_answer0 in
            let new_answer1 = answer@(List.concat new_answer0) in
            let new_lst_var = "t"^(string_of_int (new_state())) in 
            let new_answer2 = new_answer1@[new_label(),LIST_EMPTY(new_lst_var)] in
            let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
            let appended_lst = List.map (fun x -> (new_label(), LIST_APPEND(new_lst_var,x))) assigned_var_lst in
              if switch = 0 then help_translate tl (new_answer2@appended_lst) 0
              (*else if switch = 1 then help_translate tl (new_answer2@appended_lst@[assigned_var_lst])*)
              else help_translate tl (new_answer2@appended_lst@[(0,RETURN(new_lst_var))]) 0
          | Spy.Tuple(expr_lst) ->
            let new_answer0 = List.map assign_elem expr_lst in
            let assigned_lst0 = List.map get_last_elem new_answer0 in
            let new_answer1 = answer@(List.concat new_answer0) in
            let new_lst_var = "t"^(string_of_int (new_state())) in 
            let new_answer2 = new_answer1@[new_label(),TUPLE_EMPTY(new_lst_var)] in
            let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
            let appended_tuple = List.map (fun x -> (new_label(), TUPLE_INSERT(new_lst_var,x))) assigned_var_lst in
            if switch = 0 then help_translate tl (new_answer2@appended_tuple) 0
            (*else if switch = 1 then help_translate tl (new_answer2@appended_tuple@[assigned_var_lst]) 0*)
            else help_translate tl (new_answer2@appended_tuple@[(0,RETURN(new_lst_var))]) 0
          | Spy.BinOp(expr1, oper, expr2) ->
              let new_answer1 = help_translate [Expr(expr1)] answer 0 in
              let var1 = get_var_from_assign (get_last_elem new_answer1) in
              let new_answer2 = help_translate [Expr(expr2)] new_answer1 0 in
              let aug_var = get_var_from_assign (get_last_elem new_answer2) in
              if switch = 0 then
                let new_var_num = new_state() in
                match oper with 
                | Add -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),ADD,var1,aug_var))]) 0
                | Sub -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),SUB,var1,aug_var))]) 0
                | Mult -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),MUL,var1,aug_var))]) 0
                | Div -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),DIV,var1,aug_var))]) 0
                | Mod -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),MOD,var1,aug_var))]) 0
                | Pow -> help_translate tl (new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),POW,var1,aug_var))]) 0
                (*| Add -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),ADD,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]
                | Sub -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),SUB,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]
                | Mult -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),MUL,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]
                | Div -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),DIV,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]
                | Mod -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),MOD,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]
                | Pow -> new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),POW,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]*)
              else
                let new_answer1 = help_translate [Expr(expr1)] answer 0 in
                help_translate tl (help_translate [Expr(expr2)] new_answer1 0) 0

          | Spy.UnaryOp(unaryop,expr1) ->
            (*match unaryop with
              | Not -> 
              | UAdd ->
              | USub -> *)
              let new_answer1 = help_translate [Expr(expr1)] answer 0 in
              let new_var_num = new_state() in
              begin
              match unaryop with
              | Not ->
                let new_answer2 = new_answer1@[(new_label(),ASSIGNU( "t"^(string_of_int new_var_num), NOT ,"t"^(string_of_int (new_var_num-1))))] in 
                help_translate tl new_answer2 0
              | UAdd ->
                let new_answer2 = new_answer1@[(new_label(),ASSIGNU( "t"^(string_of_int new_var_num), UPLUS ,"t"^(string_of_int (new_var_num-1))))] in 
                help_translate tl new_answer2 0
              | USub -> 
                let new_answer2 = new_answer1@[(new_label(),ASSIGNU( "t"^(string_of_int new_var_num), UMINUS ,"t"^(string_of_int (new_var_num-1))))] in 
                help_translate tl new_answer2 0
              end
          | Spy.Compare(expr1,cmpoper, expr2) ->
            let new_answer1 = help_translate [Expr(expr1)] answer 0 in
            let new_answer2 = help_translate [Expr(expr2)] new_answer1 0 in
            let var1 = get_var_from_assign (get_last_elem new_answer1) in
            let aug_var = get_var_from_assign (get_last_elem new_answer2) in
            let new_var_num = new_state() in
            begin
            match cmpoper with
            | Eq ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),EQ,var1,aug_var))] in
              help_translate tl new_answer3 0
            | NotEq ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),NEQ,var1,aug_var))] in
              help_translate tl new_answer3 0
            | Lt ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),LT,var1,aug_var))] in
              help_translate tl new_answer3 0
            | LtE ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),LE,var1,aug_var))] in
              help_translate tl new_answer3 0
            | Gt ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),GT,var1,aug_var))] in
              help_translate tl new_answer3 0
            | GtE ->
              let new_answer3 = new_answer2@[(new_label(),ASSIGNV( "t"^(string_of_int new_var_num),GE,var1,aug_var))] in
              help_translate tl new_answer3 0
            (*let new_answer3 = new_answer2@[ASSIGNV( "t"^(string_of_int new_var_num),cmpoper,"t"^(string_of_int (new_var_num-2)),"t"^(string_of_int (new_var_num-1)))]*)
            end
          | Spy.IfExp(condition, true_expr, false_expr) ->
            let new_answer1 = help_translate [Expr(condition)] answer 0 in
            let condition_var = get_var_from_assign (get_last_elem new_answer1) in

            let false_label = new_label() in
            let true_label = new_label() in
            let end_label = new_label() in
            (*let new_answer1 = new_answer0@[(end_label,SKIP)] in*)
            let new_answer2 = (*new_answer1@*)[(true_label,SKIP)] in
            let new_answer3 = help_translate [Expr(true_expr)] new_answer2 0 in
            let new_answer4 = new_answer3@[(new_label(),UJUMP(end_label))] in

            let new_answer5 = new_answer4@[(false_label,SKIP)] in
            let new_answer6 = help_translate [Expr(false_expr)] new_answer5 0 in
            let new_answer7 = new_answer6@[(new_label(),UJUMP(end_label))] in

            let new_answer8 = new_answer7@[(end_label,SKIP)] in

            (*@[(false_label,SKIP)]@[(end_label,SKIP)] in*)
            let new_answer9 = new_answer1@[(new_label(),CJUMP(condition_var,true_label))] in
            let new_answer10 = new_answer9@[(new_label(),UJUMP(false_label))] in
            
            let new_answer11 = new_answer10@new_answer8 in
            help_translate tl new_answer11 0

          | Spy.Call(f,var_lst) ->
            begin
            match f with
            | Spy.Attribute(_,idf) ->
              let new_answer0 = answer@(help_translate [Expr(f)] [] 0) in
              let l_var = get_idt_from_copy (get_last_elem new_answer0) in
              if idf = "append" then 
                let answer_for_var_lst = List.map assign_elem var_lst in
                let assigned_lst0 = List.map get_last_elem answer_for_var_lst in
                let new_answer1 = new_answer0@(List.concat answer_for_var_lst) in
                let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in
                let appended_lst = List.map (fun x -> (new_label(),LIST_APPEND(l_var,x))) assigned_var_lst in
                help_translate tl (new_answer1@appended_lst) 0
              else raise (Not_Implemented "anothr built-in function!")
            | Spy.Name(_) ->
              let function_name = (get_from_name f) in
              if function_name = "print" then 
                let new_answer0 = List.map write_elem var_lst in
                let new_answer1 = answer@(List.concat new_answer0) in
                help_translate tl new_answer1 0
                (*let new_answer0 = List.map assign_elem var_lst in
                let assigned_lst0 = List.map get_last_elem new_answer0 in
                let new_answer1 = answer@(List.concat new_answer0) in
                (*let last_elem = get_last_elem new_answer1 in*)
                let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in
                let new_answer2 = List.map (fun x -> (new_label(),WRITE(x))) assigned_var_lst in
                let new_answer2 = new_answer1@[(new_label(),WRITE(assigned_last_elem))] in
                help_translate tl new_answer2 0*)
              else if function_name = "input" then
                let new_var = "t"^(string_of_int (new_state())) in
                help_translate tl (answer@[(new_label(),READ(new_var))]) 0
              else if function_name = "int" then
                let var_to_check = List.hd var_lst in
                let var_to_check0 = help_translate [Expr(var_to_check)] answer 0 in
                let var_to_check1 = get_idt_from_copy (get_last_elem var_to_check0) in
                let new_var = "t"^(string_of_int (new_state())) in
                let new_answer0 = var_to_check0@[(new_label(), INT_OF_STR(new_var,var_to_check1))] in
                help_translate tl new_answer0 0
              else if function_name = "range" then
                let answer_for_var_lst = List.map assign_elem var_lst in
                let assigned_lst0 = List.map get_last_elem answer_for_var_lst in
                let new_answer1 = answer@(List.concat answer_for_var_lst) in
                let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in
                let assigned_var = List.hd assigned_var_lst in
                let lo = List.hd (List.tl assigned_var_lst) in
                let hi = List.hd (List.rev assigned_var_lst) in
                let new_answer2 = new_answer1@[(new_label(),RANGE(assigned_var,lo,hi))] in
                help_translate tl new_answer2 0
              else
                let call_var = "t"^(string_of_int (new_state())) in
                let new_var1 = "t"^(string_of_int (new_state())) in
                (*let new_var2 = "t"^(string_of_int new_state()) in*)
                let new_answer1 = answer@[(new_label(), COPY(new_var1,(get_from_name f)))] in
                let new_answer0 = List.map assign_elem var_lst in
                (*let new_answer01 = drop_last new_answer0 in*)
                let assigned_lst0 = List.map get_last_elem new_answer0 in
                let new_answer2 = new_answer1@(List.concat new_answer0) in
                let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
                (*let new_answer2 = help_translate var_lst new_answer1 0 in
                let last_elem = get_last_elem new_answer2 in
                  if last_elem = LIST_APPEND(lst_var,_) then let tlst = lst_var in
                    let new_answer3 = new_answer2@[new_label(), COPY(new_var2,tlst)]
                    new_answer3@[new_label(), CALL(call_var,new_var1,)]
                  else last_elem = LIST_EMPTY(lst_var) then let tlst = lst_var 
                    let new_answer3 = new_answer2@[new_label(), COPY(new_var2,tlst)]*)
                help_translate tl (new_answer2@[(new_label(),CALL(call_var, new_var1,assigned_var_lst))]) 0
            | _ -> raise (Not_Implemented "call not implemented, it's not name or attribute")
          end
          | Spy.Lambda(_,_) -> raise (Not_Implemented "lambda not implemented")
          | Spy.BoolOp(boolopr, expr_lst) ->
            let l_len =  List.length expr_lst in
            if l_len = 2 then
              let new_answer0 = List.map assign_elem expr_lst in
              (*let new_answer01 = drop_last new_answer0 in*)
              let assigned_lst0 = List.map get_last_elem new_answer0 in
              let new_answer1 = answer@(List.concat new_answer0) in
              let assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
              let new_var1 = "t"^(string_of_int (new_state())) in 
                if boolopr = And then
                  let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var1, AND, get_var_from_assign (List.nth assigned_lst0 0), List.nth assigned_var_lst 1))] in
                  help_translate tl new_answer2 0
                else
                  let new_answer2 = new_answer1@[(new_label(),ASSIGNV(new_var1, OR, get_var_from_assign (List.nth assigned_lst0 0), List.nth assigned_var_lst 1))] in
                  help_translate tl new_answer2 0
            else if l_len > 2 then
              let new_answer0 = answer@(test_boolopr boolopr expr_lst) in
              help_translate tl new_answer0 0
            else raise (Not_Implemented "boolop only 1 element")
          end

            (*let false_lst = [false;CNone;0;[];();""] in
            let num_false = BatSet.intersect (BatSet.of_list expr_lst) (BatSet.of_list false_lst) in
            let num_true = BatSet.diff (BatSet.of_list expr_lst) (BatSet.of_list false_lst) in
            if boolopr = And then 
              if BatSet.Cardinal num_false >= 1 then *)


        | Spy.Assign( expr_lst , expr1 )::tl -> 
          begin
          match expr_lst with
          | [Name(idf)] ->
            begin
            match expr1 with
            | Spy.List(_)-> 
              let new_answer0 = help_translate [Expr(expr1)] answer 2 in
              let new_answer1 = drop_last new_answer0 in
              let list_var = get_last_elem new_answer0 in
              let list_var2 = get_from_return list_var in
              help_translate tl (new_answer1@[(new_label(),COPY(idf,list_var2))]) 0
            | Spy.Tuple(_) -> 
              let new_answer0 = help_translate [Expr(expr1)] answer 2 in
              let new_answer1 = drop_last new_answer0 in
              let list_var = get_last_elem new_answer0 in
              let list_var2 = get_from_return list_var in
              help_translate tl (new_answer1@[(new_label(),COPY(idf,list_var2))]) 0
            | Spy.Name(_) -> 
              let new_answer0 = help_translate [Expr(expr1)] answer 0 in
              let idf_var = get_idt_from_copy (get_last_elem new_answer0) in
              help_translate tl (new_answer0@[(new_label(),COPY(idf,idf_var))]) 0
              (*let is = new_state () in
              let new_var = Spy.Name("t"^(string_of_int is)) in
              let new_answer = (label+1, COPY(new_var, expr1))::answer in
              (label+2, COPY(idt,new_var)::new_answer)*)
            | Spy.Constant(cst) -> 
              let new_answer0 = help_translate [Expr(expr1)] answer 0 in
              let new_var = get_idt_from_copy (get_last_elem new_answer0) in
              begin
              match cst with
              | CInt(_) -> 
                let _ = prerr_endline("here0!") in
                (*let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, i1))] in*)
                help_translate tl (new_answer0@[(new_label(), COPY(idf,new_var))]) 0
              | CString(s1) -> 
                let new_answer1 = new_answer0@[(new_label(), COPYS(new_var, s1))] in
                help_translate tl (new_answer1@[(new_label(), COPY(idf,new_var))]) 0
              | CBool(b1) -> 
                if b1 = true then
                  let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 1))] in
                  help_translate tl (new_answer1@[(new_label(), COPY(idf,new_var))]) 0
                else
                  let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 0))] in
                  help_translate tl (new_answer1@[(new_label(), COPY(idf,new_var))]) 0
              | CNone -> 
                help_translate tl (new_answer0@[(new_label(), COPYN(idf))]) 0
              end
            | Spy.BoolOp(_,_) -> raise (Not_Implemented "Not implemented") 
            | Spy.BinOp(_,_,_) -> 
              let _ = prerr_endline("right is binop!") in
              let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
              let new_answer0_var = get_last_elem new_answer0 in
              let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
              let _ = prerr_endline("assign binop started!") in
              help_translate tl (new_answer0@[(new_label(), COPY(idf,new_answer0_var1))]) 0
            | Spy.UnaryOp(_,_) -> raise (Not_Implemented "Not implemented")
            | Spy.IfExp(_,_,_) -> raise (Not_Implemented "Not implemented")
            | Spy.ListComp(_,_) -> raise (Not_Implemented "Not implemented")
            | Spy.Compare(_,_,_) -> raise (Not_Implemented "Not implemented")
            | Spy.Call(_,_) -> 
              let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
              let new_answer0_var = get_last_elem new_answer0 in
              let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
              help_translate tl (new_answer0@[(new_label(), COPY(idf,new_answer0_var1))]) 0
            | Spy.Attribute(_,_) -> raise (Not_Implemented "Not implemented")
            | Spy.Subscript(_,_) -> 
              let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
              let new_answer0_var = get_last_elem new_answer0 in
              let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
              help_translate tl (new_answer0@[(new_label(), COPY(idf,new_answer0_var1))]) 0
            | Lambda(_,_) -> raise (Not_Implemented "Not implemented")
            end
              (*let newAnswer = help_translate (expr1::pgm) answer in 
                let (label,_) = if List.is_empty newAnswer then 1 else List.hd newAnswer in
                  match expr1 with
                  | Spy.UnaryOp( unaryop , expr ) -> (label+1, ASSIGNU( List.hd expr_lst ,unaryop, expr))::newAnswer
                  | Spy.Tuple ->
                  | Spy.List -> 
                  | () -> -> (label+1, COPYC())::newAnswer*)
          | [Spy.Subscript(expr01,expr02)] ->
            begin
              match expr01 with
              | Name(idf) -> 
                let new_answer0 = answer@(help_translate [Expr(expr02)] [] 0) in
                let index_var = get_idt_from_copy (get_last_elem new_answer0) in
                begin
                  match expr1 with
                  | Spy.List(_)-> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 2 in
                    let new_answer1 = drop_last new_answer0 in
                    let list_var = get_last_elem new_answer0 in
                    let list_var2 = get_from_return list_var in
                    let new_answer2 = new_answer1@[(new_label(),ITER_STORE(idf,index_var,list_var2))] in
                    help_translate tl new_answer2 0
                  | Spy.Tuple(_) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 2 in
                    let new_answer1 = drop_last new_answer0 in
                    let list_var = get_last_elem new_answer0 in
                    let list_var2 = get_from_return list_var in
                    let new_answer2 = new_answer1@[(new_label(),ITER_STORE(idf,index_var,list_var2))] in
                    help_translate tl new_answer2 0
                  | Spy.Name(_) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 0 in
                    let idf_var = get_idt_from_copy (get_last_elem new_answer0) in
                    let new_answer2 = new_answer0@[(new_label(),ITER_STORE(idf,index_var,idf_var))] in
                    help_translate tl new_answer2 0
                    (*let is = new_state () in
                    let new_var = Spy.Name("t"^(string_of_int is)) in
                    let new_answer = (label+1, COPY(new_var, expr1))::answer in
                    (label+2, COPY(idt,new_var)::new_answer)*)
                  | Spy.Constant(cst) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 0 in
                    let new_var = get_idt_from_copy (get_last_elem new_answer0) in
                    begin
                    match cst with
                    | CInt(_) -> 
                      let _ = prerr_endline("here0!") in
                      (*let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, i1))] in*)
                      help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CString(s1) -> 
                      let new_answer1 = new_answer0@[(new_label(), COPYS(new_var, s1))] in
                      help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CBool(b1) -> 
                      if b1 = true then
                        let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 1))] in
                        help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                      else
                        let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 0))] in
                        help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CNone -> 
                      help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    end
                  | Spy.BoolOp(_,_) -> raise (Not_Implemented "Not implemented") 
                  | Spy.BinOp(_,_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Spy.UnaryOp(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.IfExp(_,_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.ListComp(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Compare(_,_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Call(_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Spy.Attribute(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Subscript(_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Lambda(_,_) -> raise (Not_Implemented "Not implemented")
                  end
              | _ ->
                let new_answer0 = answer@(help_translate [Expr(expr02)] [] 0) in
                let index_var = get_idt_from_copy (get_last_elem new_answer0) in
                let new_answer1 = new_answer0@(help_translate [Expr(expr01)] [] 0) in
                let idf = get_idt_from_copy (get_last_elem new_answer1) in
                begin
                  match expr1 with
                  | Spy.List(_)-> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 2 in
                    let new_answer1 = drop_last new_answer0 in
                    let list_var = get_last_elem new_answer0 in
                    let list_var2 = get_from_return list_var in
                    let new_answer2 = new_answer1@[(new_label(),ITER_STORE(idf,index_var,list_var2))] in
                    help_translate tl new_answer2 0
                  | Spy.Tuple(_) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 2 in
                    let new_answer1 = drop_last new_answer0 in
                    let list_var = get_last_elem new_answer0 in
                    let list_var2 = get_from_return list_var in
                    let new_answer2 = new_answer1@[(new_label(),ITER_STORE(idf,index_var,list_var2))] in
                    help_translate tl new_answer2 0
                  | Spy.Name(_) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 0 in
                    let idf_var = get_idt_from_copy (get_last_elem new_answer0) in
                    let new_answer2 = new_answer0@[(new_label(),ITER_STORE(idf,index_var,idf_var))] in
                    help_translate tl new_answer2 0
                    (*let is = new_state () in
                    let new_var = Spy.Name("t"^(string_of_int is)) in
                    let new_answer = (label+1, COPY(new_var, expr1))::answer in
                    (label+2, COPY(idt,new_var)::new_answer)*)
                  | Spy.Constant(cst) -> 
                    let new_answer0 = help_translate [Expr(expr1)] answer 0 in
                    let new_var = get_idt_from_copy (get_last_elem new_answer0) in
                    begin
                    match cst with
                    | CInt(_) -> 
                      let _ = prerr_endline("here0!") in
                      (*let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, i1))] in*)
                      help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CString(s1) -> 
                      let new_answer1 = new_answer0@[(new_label(), COPYS(new_var, s1))] in
                      help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CBool(b1) -> 
                      if b1 = true then
                        let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 1))] in
                        help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                      else
                        let new_answer1 = new_answer0@[(new_label(), COPYC(new_var, 0))] in
                        help_translate tl (new_answer1@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    | CNone -> 
                      help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_var))]) 0
                    end
                  | Spy.BoolOp(_,_) -> raise (Not_Implemented "Not implemented") 
                  | Spy.BinOp(_,_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Spy.UnaryOp(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.IfExp(_,_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.ListComp(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Compare(_,_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Call(_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Spy.Attribute(_,_) -> raise (Not_Implemented "Not implemented")
                  | Spy.Subscript(_,_) -> 
                    let new_answer0 = answer@(help_translate [Expr(expr1)] [] 0) in
                    let new_answer0_var = get_last_elem new_answer0 in
                    let new_answer0_var1 = get_idt_from_copy new_answer0_var in 
                    help_translate tl (new_answer0@[(new_label(), ITER_STORE(idf,index_var,new_answer0_var1))]) 0
                  | Lambda(_,_) -> raise (Not_Implemented "Not implemented")
                  end
                
          
              end
            

          | _ ->
            if (List.length expr_lst) >= 1 then
              begin
              match expr1 with 
              | Spy.List(_) | Spy.Tuple(_)  ->
                let unpacked_left = unpack_all expr_lst in
                let assignment_left = List.map assign_elem unpacked_left in
                let new_answer1 = answer@(List.concat assignment_left) in
                let assigned_lst0 = List.map get_last_elem assignment_left in
                let left_assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
                let unpacked_right = unpack_all [expr1] in
                let assignment_right = List.map assign_elem unpacked_right in
                let new_answer2 = new_answer1@(List.concat assignment_right) in
                let assigned_lst1 = List.map get_last_elem assignment_right in
                let right_assigned_var_lst = List.map get_idt_from_copy assigned_lst1 in
                (*if (List.length expr_lst = List.length right_lst) then*)
                let paired_lst = zip left_assigned_var_lst right_assigned_var_lst in
                let paired_lst2 = List.map assign_fun paired_lst in
                (*let paired_lst = zip (unpack_all expr_lst) (unpack_all [expr1]) in
                let paired_lst2 = List.map assign_fun paired_lst in*)
                help_translate ((paired_lst2)@tl) new_answer2 0
              | Spy.Constant(CString(_)) ->
                (*match expr1 with
                  | string -> *)
                  let unpacked_left = unpack_all expr_lst in
                  let assignment_left = List.map assign_elem unpacked_left in
                  let new_answer1 = answer@(List.concat assignment_left) in
                  let assigned_lst0 = List.map get_last_elem assignment_left in
                  let left_assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in 
                  let string_lst = get_string_from_constant expr1 |> String.to_seq |> List.of_seq in
                  let string_lst1 = List.map Char.escaped string_lst in 
                  (*let string_lst2 = List.map (fun x -> Spy.Constant(CString(x))) string_lst1 in*)
                  let paired_lst = zip left_assigned_var_lst (string_lst1) in
                  let paired_lst2 = List.map assign_fun paired_lst in
                  help_translate ((paired_lst2)@tl) new_answer1 0
              | Spy.Name(_) ->
                let iter_index = ref ~-1 in
                let new_index() = iter_index := !iter_index + 1; !iter_index in
                let unpacked_left = unpack_all expr_lst in
                let assignment_left = List.map assign_elem unpacked_left in
                let new_answer1 = answer@(List.concat assignment_left) in
                let assigned_lst0 = List.map get_last_elem assignment_left in
                let left_assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in
                let new_answer2 = new_answer1@(help_translate [Expr(expr1)] [] 0) in
                let right_val = get_last_elem new_answer2 in
                let right_val1 = get_var_from_assign right_val in

                let index_lst = List.init (List.length unpacked_left) (fun x -> x) in
                let index_lst0 = List.map (fun x -> (new_label(),COPYC("t"^string_of_int (new_state()),x))) index_lst in
                let index_lst1 = List.map get_idt_from_copy index_lst0 in

                let load_lst = List.map (fun x -> (new_label(),ITER_LOAD(x,right_val1, List.nth index_lst1 (new_index()) ))) left_assigned_var_lst in
                let new_answer3 = new_answer2@load_lst in
                help_translate tl new_answer3 0 
              | Spy.Call(_,_) -> raise (Not_Implemented "Not implemented on call")
              | Spy.Constant(CBool(_)) -> raise (Not_Implemented "Not implemented on cbool") 
              | Spy.Constant(CInt(_)) ->
                let unpacked_left = unpack_all expr_lst in
                let assignment_left = List.map assign_elem unpacked_left in
                let new_answer0 = answer@(List.concat assignment_left) in
                let assigned_lst0 = List.map get_last_elem assignment_left in
                let left_assigned_var_lst = List.map get_idt_from_copy assigned_lst0 in
                let new_answer1 = help_translate [Expr(expr1)] new_answer0 0 in
                let new_var = get_idt_from_copy (get_last_elem new_answer1) in
                let assigned_lst1 = List.map (fun x -> (new_label(),COPY(x,new_var))) left_assigned_var_lst in
                let new_answer1 = new_answer1@assigned_lst1 in
                help_translate tl new_answer1 0
              | Spy.Constant(CNone) -> raise (Not_Implemented "Not implemented on cnone") 
              | _ -> raise (Not_Implemented "Not implemented on others")
              end
            else raise (Not_Implemented "Not implemented on left2")
          end

              (*let new_answer0 = help_translate [Expr(expr1)] answer 0 in
              let expr_var = get_last_elem new_answer0 in
              let expr_var2 = get_var_from_assign expr_var in
              let new_answer1 = help_translate []*)
              (*let found_lst1 = List.find_all(fun spy_cm -> spy_cm = COPY(_,_)) in
              let found_lst2 = List.find_all(fun (el,_) -> el = expr1 ) in
              let name_value = List.hd (List.rev found_lst2) in
                match name_value with
                | Spy.List(_)->
                  let new_answer0 = help_translate [expr1] answer 2 in
                  let new_answer1 = drop_last new_answer0 in
                  let list_var = get_last_elem new_answer0 in
                  let list_var2 = get_from_return list_var in
                  help_translate tl (new_answer1@[(new_label(),COPY(idf,list_var2))]) 0
                | Spy.Tuple(_) -> 
                  let new_answer0 = help_translate [expr1] answer 2 in
                  let new_answer1 = drop_last new_answer0 in
                  let list_var = get_last_elem new_answer0 in
                  let list_var2 = get_from_return list_var in
                  help_translate tl (new_answer1@[(new_label(),COPY(idf,list_var2))]) 0*)
        | Spy.While(condition, stmt_lst)::tl ->
          let condition_label = new_label() in
          let end_label = new_label() in

          let new_answer0 = answer@[(condition_label,SKIP)] in
          let new_answer1 = help_translate [Expr(condition)] new_answer0 0 in
          let condition_var = get_var_from_assign (get_last_elem new_answer1) in

          let insert_elem = Expr(Constant(CInt(condition_label))) in
          let insert_elem1 = Expr(Constant(CInt(end_label))) in
          let stmt_lst2 = insert_after stmt_lst Continue insert_elem in
          let stmt_lst3 = insert_after stmt_lst2 Break insert_elem1 in
          let _ = prerr_endline("i'll show you stmt_lst from while!") in
          let new_answer2 = help_translate stmt_lst3 [] 0 in
          let _ = List.map print_instr_from_linstr new_answer2 in
          let new_answer3 = new_answer2@[(new_label(),UJUMP(condition_label))] in
          let new_answer4 = new_answer3@[(end_label,SKIP)] in

          let new_answer5 = new_answer1@[(new_label(),CJUMPF(condition_var,end_label))] in
          let new_answer6 = new_answer5@new_answer4 in
          help_translate tl new_answer6 0 
          
        | Spy.If(condition, true_lst, false_lst)::tl ->
          let new_answer1 = help_translate [Expr(condition)] answer 0 in
          let condition_var = get_var_from_assign (get_last_elem new_answer1) in

          let false_label = new_label() in
          let true_label = new_label() in
          let end_label = new_label() in

          let new_answer2 = (*new_answer1@*)[(true_label,SKIP)] in
          let new_answer3 = help_translate true_lst new_answer2 0 in
          let new_answer4 = new_answer3@[(new_label(),UJUMP(end_label))] in

          let new_answer5 = new_answer4@[(false_label,SKIP)] in
          let new_answer6 = help_translate false_lst new_answer5 0 in
          let new_answer7 = new_answer6@[(new_label(),UJUMP(end_label))] in

          let new_answer8 = new_answer7@[(end_label,SKIP)] in

          (*@[(false_label,SKIP)]@[(end_label,SKIP)] in*)
          let new_answer9 = new_answer1@[(new_label(),CJUMP(condition_var,true_label))] in
          let new_answer10 = new_answer9@[(new_label(),UJUMP(false_label))] in
          
          let new_answer11 = new_answer10@new_answer8 in
          help_translate tl new_answer11 0 
        | Spy.Return(Some expr)::tl ->
          begin
          match expr with
          | Constant(CNone) -> help_translate tl answer 0
          | _ -> 
            let new_answer1 = help_translate [Expr(expr)] answer 0 in
            let return_var = get_var_from_assign (get_last_elem new_answer1) in
            let new_answer2 = new_answer1@[(new_label(), RETURN(return_var))] in
            help_translate tl new_answer2 0
          end
        | FunctionDef(fname,var_lst,stmt_lst)::tl ->
          let new_answer0 = help_translate stmt_lst [] 0 in
          let new_answer1 = answer@new_answer0 in
          let new_answer2 = [(new_label(),FUNC_DEF(fname,var_lst,new_answer0))]@new_answer1 in
          help_translate tl new_answer2 0
        | AugAssign(var,oper,aug)::tl ->
          let _ = prerr_endline("AugAssign started! yayyy") in
          let new_answer1 = help_translate [Expr(var)] answer 0 in
          let _ = prerr_endline("let me show you new_answer1 from augassign") in
          let _ = List.map print_instr_from_linstr new_answer1 in
          let var1 = get_var_from_assign (get_last_elem new_answer1) in
          let _ = prerr_endline("var1:"^var1) in
          let new_answer2 = help_translate [Expr(aug)] new_answer1 0 in
          let _ = prerr_endline("let me show you new_answer2 from augassign") in
          let _ = List.map print_instr_from_linstr new_answer2 in
          let aug_var = get_var_from_assign (get_last_elem new_answer2) in
          let new_var_num = new_state() in
          let new_var = "t"^(string_of_int (new_var_num)) in
          let var2 = get_string_from_idt var in
          begin
          match oper with
          | Add -> 
            let _ = prerr_endline("AugAssign_Add started!") in
            let new_answer3 = (new_answer2@[(new_label(), ASSIGNV( new_var,ADD,var1,aug_var))]) in
            let _ = prerr_endline("let me show you new_answer3 from augassign") in
            let _ = List.map print_instr_from_linstr new_answer3 in
            let new_answer4 = (new_answer3@[(new_label(),COPY(var2,new_var))]) in
            let _ = prerr_endline("let me show you new_answer4 from augassign") in
            let _ = List.map print_instr_from_linstr new_answer4 in
            let new_answer5 = help_translate tl new_answer4 0 in
            let _ = prerr_endline("let me show you new_answer5 from augassign") in
            let _ = List.map print_instr_from_linstr new_answer5 in
            new_answer5
          | Sub ->  
            let new_answer3 = (new_answer2@[(new_label(),ASSIGNV( new_var,SUB,var1,aug_var))]) in
            help_translate tl (new_answer3@[(new_label(),COPY(var2,new_var))]) 0
          | Mult ->  
            let new_answer3 = (new_answer2@[(new_label(),ASSIGNV( new_var,MUL,var1,aug_var))]) in
            help_translate tl (new_answer3@[(new_label(),COPY(var2,new_var))]) 0
          | Div -> 
            let new_answer3 = (new_answer2@[(new_label(),ASSIGNV( new_var,DIV,var1,aug_var))]) in
            help_translate tl (new_answer3@[(new_label(),COPY(var2,new_var))]) 0
          | Mod -> 
            let new_answer3 = (new_answer2@[(new_label(),ASSIGNV( new_var,MOD,var1,aug_var))]) in
            help_translate tl (new_answer3@[(new_label(),COPY(var2,new_var))]) 0
          | Pow -> 
            let new_answer3 = (new_answer2@[(new_label(),ASSIGNV( new_var,POW,var1,aug_var))]) in
            help_translate tl (new_answer3@[(new_label(),COPY(var2,new_var))]) 0
          end
        | Assert(expr0)::tl -> 
          let new_answer0 = help_translate [Expr(expr0)] answer 0 in
          let assert_var = get_idt_from_copy (get_last_elem new_answer0) in
          let new_answer1 = new_answer0@[(new_label(),ASSERT(assert_var))] in
          help_translate tl new_answer1 0
        | Break::tl0 -> 
          let end_label = get_constant_from_expr (List.hd tl0) in
          let new_answer0 = answer@[(new_label(),UJUMP(end_label))] in
          help_translate (List.tl tl0) new_answer0 0
        | Continue::tl0 -> 
          let condition_label = get_constant_from_expr (List.hd tl0) in
          let new_answer0 = answer@[(new_label(),UJUMP(condition_label))] in
          help_translate (List.tl tl0) new_answer0 0
        | Pass::_ -> raise (Not_Implemented "Pass Not implemented")
        | (*For(expr,iter,stmt_lst)*)For(_,_,_)::_ -> raise (Not_Implemented "For Not implemented")
          (*let new_answer0 = (help_translate [Expr(expr)] answer 0 ) in
          let expr_var = get_idt_from_copy (get_last_elem new_answer0) in
          let new_answer1 = new_answer0(help_translate [Expr(iter)] answer 0)
          let iter_var = get_idt_from_copy (get_last_elem new_answer1) in
          match iter with
          | List(expr_lst) -> 
            let iter_num = List.length expr_lst in
            let cmp_var = "t"^(string_of_int new_state() ) in
            let init_cmp_var = Assign([cmp_var],Constant(Cint(0))) in
            let conditon = (new_label(),ASSIGNV )(Name(cmp_var),Lt,iter_num) in
            let init_expr = *)




        | _ -> raise (Not_Implemented "Not implemented on left4")
    in
    (help_translate spyPgm [] 0)@[(new_label(),HALT)]