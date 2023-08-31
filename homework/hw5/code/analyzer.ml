let type_index = ref 1
let new_type() = type_index := !type_index + 1; (*"T" ^ (string_of_int*) !type_index

type type_idf = string*int
type arg = string list

exception Not_Implemented of string 
exception Error of string


type t = 
| TYPE_IDF of type_idf
| FUNC of t*arg*(type_elem list)
| ARRAY of string*int
| CONSTANT of Spy.constant
| CFloat of float
(*| Input*)

and  type_elem = string * t

type list_elem = string*int
type before_answer = t

type table_answer = bool*(type_elem list)
type single_answer = before_answer * table_answer

let rec analyze : Spy.program -> Spvm.program -> bool = fun (spy_pgm) _  ->
  (*let _ = List.iter (fun x -> print_endline (string_of_stmt x)) spy_pgm in*)
  let (no_error, _ ) = analyze_stmts spy_pgm [] in
  no_error

and get_first_from_type_table : table_answer -> bool = fun ans ->
  let (no_error,_) = ans in
  no_error

and string_of_type : t -> string = fun ty ->
  match ty with
  | TYPE_IDF((s,n))
    -> s^(string_of_int n)
  | FUNC(_,_,_)
    -> "function"
  | ARRAY(x,n)
    -> x^"is array whose length is"^(string_of_int n)
  | CONSTANT(c) ->
    begin
      match c with
      | CInt(_) -> "int!"
      | CBool(_) -> "bool!"
      | CNone -> "none!"
      | CString(_) -> "string!"
    end
  | CFloat(_) -> "float!"

and string_of_stmt : Spy.stmt -> string = fun stmt ->
  match stmt with 
  | FunctionDef(f,_,_) -> "def"^" "^f^"~"
  | Return(r_val) -> 
    begin
    match r_val with 
    | None -> "return nothing"
    | Some x -> "return"^(string_of_expr x)
    end
  | Assign(targets,rhs) -> 
    let string_expr_lst = List.map string_of_expr targets in
    let concatenated_args = String.concat "," string_expr_lst in
    let string_rhs = string_of_expr rhs in
    concatenated_args ^ "=" ^ string_rhs
  | AugAssign(target,op,value) ->
    let string_target = (string_of_expr target) in
    string_target ^ "=" ^ string_target ^ (string_of_op op) ^ (string_of_expr value)
  | For(_,_,_) -> raise (Error "for not Implemented")
  | While(test,body) -> 
    let string_test = string_of_expr test in
    let string_stmt_lst = List.map string_of_stmt body in
    let concatenated_args = String.concat "\n" string_stmt_lst in
    "while"^" "^string_test^":"^"\n"^"    "^concatenated_args
  | If(test,body,orelse) ->
    let string_test = string_of_expr test in
    let string_body_lst = List.map string_of_stmt body in
    let string_orelse_lst = List.map string_of_stmt orelse in
    let concatenated_body_args = String.concat "\n" string_body_lst in
    let concatenated_orelse_args = String.concat "\n" string_orelse_lst in
    "If"^" "^string_test^":"^"\n"^"   "^concatenated_body_args^"\n"^"else :"^"\n"^"   "^concatenated_orelse_args
  | Assert(_) -> raise (Error "assert not Implemented")
  | Expr(expr) -> string_of_expr expr
  | Break ->  raise (Error "break not Implemented")
  | Pass 
  | Continue -> raise (Error "pass,continue not Implemented")   

and string_of_op o = 
  match o with 
  | Add -> "+" 
  | Sub -> "-" 
  | Mult -> "*" 
  | Div -> "/" 
  | Mod -> "%"
  | Pow -> "**"

and string_of_uop o =
  match o with
  | Spy.Not -> "!" 
  | UAdd -> "+"
  | USub -> "-"

and string_of_cmpop o = 
  match o with
  | Spy.Lt -> "<" 
  | LtE -> "<=" 
  | Gt -> ">" 
  | GtE -> ">=" 
  | Eq -> "==" 
  | NotEq -> "!="

and string_of_boolop o =
  match o with
  | Spy.And -> "&&" 
  | Or -> "||" 

and string_of_expr : Spy.expr -> string = fun expr1 ->
  match expr1 with
  | BoolOp(_,_) -> raise (Error "boolop function not Implemented")
  | BinOp(left,operator,right) -> (string_of_expr left)^(string_of_op operator)^(string_of_expr right)
  | UnaryOp(unaryop,expr) -> (string_of_uop unaryop)^(string_of_expr expr)
  | IfExp(condition,body,orelse) -> "If"^" "^(string_of_expr condition)^"then"^" "^(string_of_expr body)^"else"^" "^(string_of_expr orelse)
  | ListComp (_,_) -> "false"
  | Compare(left,cmpop,right) -> (string_of_expr left)^" "^(string_of_cmpop cmpop)^" "^(string_of_expr right)
  | Call(f,args) ->
    let string_expr_lst = List.map string_of_expr args in
    let concatenated_args = String.concat "," string_expr_lst in
    let function_string = string_of_expr f in
    (function_string) ^ "("^(concatenated_args)^")"
  | Constant(constant) ->
    begin
    match constant with
    | CInt(c) -> string_of_int c
    | CString(s) -> s
    | CBool(b) ->
      if b = true then "true"
      else "false"
    | CNone -> "none"
    end
  | Attribute(_,_) -> "false"
  | Subscript(array,idx) -> (string_of_expr array)^"["^(string_of_expr idx)^"]"
  | Name(identifier) -> identifier
  | List(args) ->
    let string_expr_lst = List.map string_of_expr args in
    let concatenated_args = String.concat "," string_expr_lst in
    "[" ^ concatenated_args ^ "]"
  | Tuple(args) ->
    let string_expr_lst = List.map string_of_expr args in
    let concatenated_args = String.concat "," string_expr_lst in
    "(" ^ concatenated_args ^ ")"
  | Lambda(_,_) -> "false"

and analyze_stmts : Spy.program -> type_elem list -> table_answer = fun (spy_pgm) (type_table) ->
  match spy_pgm with
  | [] -> (true,type_table)
  | hd::tl ->
    let (no_error, new_type_table) = analyze_stmt hd (type_table) in
    if no_error = false then
      (false , new_type_table)
    else analyze_stmts tl new_type_table

and find_if_exist : string -> type_elem list -> type_elem = fun var type_table ->
  let var_lst = List.find_all (fun (v,_) -> v = var ) type_table in
  if List.length var_lst = 0 then ("CONSTANT(CNone)", CONSTANT(CNone)) 
  else List.hd var_lst

and find_return_type : Spy.stmt -> bool =  fun stmt ->
  match stmt with
  | Return(_) -> true
  | _ -> false

and analyze_stmt : Spy.stmt -> type_elem list -> table_answer = fun (spy_stmt) (type_table)  ->
  match spy_stmt with
  | FunctionDef (f, args, body) -> 
    let args_type = List.map (fun x -> (x,TYPE_IDF("T",new_type()))) args in
    let (no_error,f_type_table) = analyze_stmts body (args_type) in
    if no_error = true then
      let return_list = List.find_all (find_return_type) body in
      if (List.length return_list) = 0 then 
        (true,type_table @ [(f, FUNC(CONSTANT(CNone),args,f_type_table))])
      else
        let return_elem = List.hd return_list in
        begin
        match return_elem with
        | Return r_value ->
          begin
          match r_value with
          | None -> (true, type_table @ [(f,FUNC(CONSTANT(CNone),args,f_type_table))])
          | Some x ->
            let (r_value_type,(no_error,_)) = analyze_expr x (type_table) in
            if no_error = true then (true, type_table @ [(f,FUNC(r_value_type,args,f_type_table))])
            else (false,type_table)
          end
        | _ -> (false,type_table)
        end
    else (false,type_table)
  | Return r_val -> 
    begin
    match r_val with
    | None -> (true,type_table)
    | Some x ->
      let (no_error, new_type_table) = analyze_return_stmt x (type_table) in
      if no_error = false then (false, new_type_table)
      else (true, new_type_table)
    end
  | Assign (targets, value) -> 
    let (no_error, new_type_table) = analyze_assign_stmt targets value (type_table) (true,type_table) in
    if no_error = false then (false, new_type_table)
    else (true, new_type_table)
  | AugAssign (target, op, value) -> 
    let (no_error, new_type_table) = analyze_augassign_stmt target op value (type_table) in
    if no_error = false then (false, new_type_table)
    else (true, new_type_table)
  | Expr expr -> analyze_expr_stmt expr type_table
  | If (test, body, orelse) -> 
    let (no_error, new_type_table) = analyze_if_stmt test body orelse (type_table) in
    if no_error = false then (false, new_type_table)
    else (true, new_type_table)
  | While (test, body) -> 
    let (no_error, new_type_table) = analyze_while_stmt test body (type_table) in
    if no_error = false then (false, new_type_table)
    else (true, new_type_table)
  | For (_, _, _) -> (false,type_table)
  | Break -> (true,type_table)
  | Continue -> (true,type_table)
  | Pass -> (true,type_table)
  | Assert _ -> (true,type_table)


(*and analyze_fundef : string -> Spy.stmt list -> type_elem list -> int = fun v type_table ->
  let (var, t) = find_if_exist v type_table in
  match t with
  | CONSTANT(CNone) -> 1
  | TYPE_IDF(t,n) -> 2
  | CString(s) -> 3
  | _ -> 0*)
and analyze_return_stmt : Spy.expr -> type_elem list -> table_answer = fun r_value type_table ->
  let (_,(no_error,new_type_table)) = analyze_expr (r_value) (type_table) in
  (no_error, new_type_table)
and analyze_augassign_stmt : Spy.expr -> Spy.operator -> Spy.expr -> type_elem list  -> table_answer = fun target op value type_table -> 
  analyze_assign_stmt [target] (BinOp (target, op, value)) (type_table) (true,type_table)

and analyze_while_stmt : Spy.expr -> Spy.program -> type_elem list -> table_answer = fun condition body type_table ->
  let (condition_type,(no_error1,new_type_table0)) = analyze_expr condition type_table in
  let (no_error2,new_type_table1) = analyze_stmts body new_type_table0 in
  if (no_error1 = false) || (no_error2 = false) then 
    (false,type_table)
  else
    match condition_type with 
      | CONSTANT(CBool(_)) ->
        (true,new_type_table1)
      | _ -> 
        (false,type_table)

and analyze_if_stmt : Spy.expr -> Spy.program -> Spy.program -> type_elem list -> table_answer = fun condition body orelse type_table ->
  let (condition_type,(no_error1,new_type_table0)) = analyze_expr condition type_table in
  let (no_error2,new_type_table1) = analyze_stmts body new_type_table0 in
  let (no_error3,new_type_table2) = analyze_stmts orelse new_type_table1 in
  if (no_error1 = false) || (no_error2 = false) || (no_error3 = false) then 
    (false,type_table)
  else
    match condition_type with 
      | CONSTANT(CBool(_)) ->
        (true,new_type_table2)
      | _ ->
        (false,type_table)


and analyze_assign_stmt : Spy.expr list -> Spy.expr -> type_elem list -> table_answer -> table_answer = fun targets rhs (type_table) ans ->
  match targets with
  | [] -> ans
  | hd::tl ->
    let (no_error, new_type_table) = analyze_assign_single hd rhs type_table in
    if no_error = true then analyze_assign_stmt tl rhs (new_type_table) (true,new_type_table)
    else 
      (false,new_type_table)

and analyze_expr_stmt : Spy.expr -> type_elem list -> table_answer = fun rhs type_table ->
  let (_, (no_error,new_type_table)) = analyze_expr rhs type_table in 
  (no_error, new_type_table)
(*list_fold (fun target code -> code @ translate_assign_single target rhs type_table) targets []*)

and load_list_element : Spy.expr -> single_answer list -> int -> table_answer -> table_answer = fun expr (ans_lst) idx (ans) ->
  let (_,type_table) = ans in
  match ans_lst with
  | [] -> ans
  | hd::tl ->
    let (right_type,(_,_)) = hd in
    match expr with
    | Name x -> 
      let new_type_var = x^"["^(string_of_int idx)^"]" in
      let (_,new_type) = find_if_exist new_type_var type_table in
      begin
      match new_type with
      | (CONSTANT(CNone)) ->
        let new_type_elem = (new_type_var,right_type) in
        let new_type_table = type_table @ [new_type_elem] in
        load_list_element expr tl (idx+1) (true,new_type_table)
      | _ ->
        let new_type_table = List.map (fun (v,a) -> if v = new_type_var then (v,right_type) else (v,a) ) type_table in
        load_list_element expr tl (idx+1) (true,new_type_table)
      end
    | _ -> ans

and analyze_assign_single : Spy.expr -> Spy.expr -> type_elem list -> table_answer = fun target rhs (type_table) -> 
  let (right_type, (_,new_type_table0)) = analyze_expr rhs type_table in 
  match rhs with
  | List(exprs) 
  | Tuple(exprs) ->
    let (_,(no_error1,new_type_table01)) = analyze_expr rhs new_type_table0 in
    (*(no_error1, new_type_table01)*)
    if no_error1 = false then (false,new_type_table01)
    else
      begin
      match target with
      | Name x ->
        let ((*left_var*)_,left_type) = find_if_exist x new_type_table01 in
        begin
        match left_type with
        | (CONSTANT(CNone)) ->
          let new_type_elem = (x, ARRAY(x,List.length exprs)) in
          let new_type_table = new_type_table01 @ [new_type_elem] in
          let type_table_for_lst = List.map (fun x -> analyze_expr x new_type_table) exprs in
          let (_,new_type_table2) = load_list_element target (type_table_for_lst) 0 (true,new_type_table) in
          (true,new_type_table2) 
        | _ ->
          let new_type_table = List.map (fun (v,a) -> if v = x then (v,ARRAY(x,List.length exprs)) else (v,a)) new_type_table01 in
          let type_table_for_lst = List.map (fun x -> analyze_expr x new_type_table) exprs in
          let (_, new_type_table2) = load_list_element target (type_table_for_lst) 0 (true,new_type_table01) in
          (true,new_type_table2)
        end
      | _ -> (true,type_table)
      end
  | _ -> 
    match target with 
    | Name x -> 
      let (left_var,left_type) = find_if_exist x new_type_table0 in
      begin
      match left_type with
      | CONSTANT(CNone) ->
        (*let new_type_idf = TYPE_IDF("T",new_type()) in*)
        let new_type_elem = (x, right_type) in
        let new_type_table = new_type_table0 @ [new_type_elem] in
        (true, new_type_table)
      | TYPE_IDF(_,_) ->
        let new_type_table = List.map (fun (a,t) -> if t = left_type then (a,right_type) else (a,t)) new_type_table0 in
        (true, new_type_table)
      | _ ->
        let new_type_table = List.map (fun (v,t) -> if v = left_var then (left_var,right_type) else (v,t)) new_type_table0 in
        (true, new_type_table)
      end
    | Tuple _ 
    | List _ -> (true,type_table)
    | _ -> (true,type_table)


and analyze_expr : Spy.expr -> type_elem list -> single_answer = fun rhs (type_table) -> 
  (*let (_,left_type) = find_if_exist target type_table in*)
  match rhs with
  | Name id ->
    let (_, right_type) = find_if_exist id type_table in
    begin
    match right_type with
    | (CONSTANT(CNone)) ->
      let new_type_idf = TYPE_IDF("T",new_type()) in
      let new_type_elem = (id, new_type_idf) in
      let new_type_table = type_table @ [new_type_elem] in
      (*let new_type_table2 = List.map (fun (_,t) -> if t = left_type then (_,new_type_idf)) new_type_table in*)
      (new_type_idf, (true,new_type_table))
    | _ -> 
      (*let new_type_table = List.map (fun (_,t) -> if t = left_type then (_,right_type)) type_table in*)
      (right_type,(true,type_table))
    end
  | Constant(c) -> (CONSTANT(c), (true,type_table))  
  (*| Constant c -> 
    match c with 
    | CONSTANT(CInt(_)) -> 
      match left_type with
      | CONSTANT(CInt(_)) -> (true,type_table)
      | TYPE_IDF(_,_) -> 
        let new_type_table = List.map (fun (_,t) -> if t = left_type then (_,right_type)) type_table in
        (true,new_type_table)
      (*| CONSTANT(CNone) -> 
        let new_type_elem = (target,right_type) in
        let new_type_table = type_table @ [new_type_elem]
        (true,new_type_table)*)
      | _ -> (false,type_table)
    | CBool(_) -> 
      match left_type with
      | CBool(_) -> (true,type_table)
      | TYPE_IDF(_,_) -> 
        let new_type_table = List.map (fun (_,t) -> if t = left_type then (_,right_type)) type_table in
        (true,new_type_table)
      (*| CONSTANT(CNone) -> 
        let new_type_elem = (target,right_type) in
        let new_type_table = type_table @ [new_type_elem]
        (true,new_type_table)*)
      | _ -> (false,type_table)
    | CString(_)->
      match left_type with
      | CString(_) -> (true,type_table)
      | TYPE_IDF(_,_) -> 
        let new_type_table = List.map (fun (_,t) -> if t = left_type then (_,right_type)) type_table in
        (true,new_type_table)
      (*| CONSTANT(CNone) -> 
        let new_type_elem = (target,right_type) in
        let new_type_table = type_table @ [new_type_elem]
        (true,new_type_table)*)
      | _ -> (false,type_table) 
    (*| _ -> raise (Error "not constant")*)
    end*)
  | UnaryOp (uop, operand) -> 
    begin
    match uop with
    | Not ->
      (CONSTANT(CBool(true)),(true,type_table))
    | UAdd
    | USub -> 
      let (operand_type, (no_error,_)) = analyze_expr operand type_table in
      if (no_error = false) then
        match operand_type with
        | CONSTANT(CInt(c)) -> (CONSTANT(CInt(c)),(true,type_table))
        | _ -> (CONSTANT(CNone),(false,type_table))
      else
        (CONSTANT(CNone),(false,type_table))
    end
  | BinOp (left, (*op*)_, right) ->
    let (left_binary_type,(no_error1,_)) = analyze_expr left type_table in
    let (right_binary_type,(no_error2,_)) = analyze_expr right type_table in
    if (no_error1 = false) || (no_error2 = false) then ((CONSTANT(CNone)),(false,type_table))
    else
      begin
      match left_binary_type with
      | CONSTANT(CInt(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CInt(_) -> (CONSTANT(b),(true,type_table))
          | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | CFloat(b) -> (CFloat(b),(true,type_table))
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (left_binary_type,(true,new_type_table))
        | FUNC(t,_,_) -> 
          begin
          match t with
          | CONSTANT(CInt(_)) -> (t,(true,type_table))
          | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | ARRAY(_,_) -> (CONSTANT(CNone),(false,type_table))
        end
      | CONSTANT(CBool(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CBool(_) -> (CONSTANT(b),(true,type_table))
          | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (left_binary_type,(true,new_type_table))
        | FUNC(t,_,_) ->
          begin
            match t with
            | CONSTANT(CBool(_)) -> (t,(true,type_table))
            | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | CFloat(_) 
        | ARRAY(_,_) -> (CONSTANT(CNone),(false,type_table))
        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | CONSTANT(CString(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CString(_) -> (CONSTANT(b),(true,type_table))
          | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (left_binary_type,(true,new_type_table))
        | FUNC(t,_,_) ->
          begin
            match t with
            | CONSTANT(CString(_)) -> (t,(true,type_table))
            | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | CFloat(_)
        | ARRAY(_,_) -> (CONSTANT(CNone),(false,type_table))
        (*| CONSTANT(CNone) -> (true,type_table)*)
        end
      | TYPE_IDF(_,n1) ->
        begin
        match right_binary_type with
        | CONSTANT(_) -> 
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (right_binary_type,(true,new_type_table))
        | TYPE_IDF(_,n2) ->
          if n1 = n2 then (left_binary_type,(true,type_table))
          else 
            let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
            (right_binary_type,(true,new_type_table))
        | FUNC(t,_,_) ->
            let new_type_table = List.map (fun (v,t1) -> if t1 = left_binary_type then (v,t) else (v,t1)) type_table in
            (t,(true,new_type_table))
        | ARRAY(_,_) ->
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (right_binary_type,(true,new_type_table))
        (*| CONSTANT(CNone) -> (true,type_table)*)
        | CFloat(_) ->
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (right_binary_type,(true,new_type_table))
        end
      | FUNC(t1,_,_) ->
        begin
        match right_binary_type with
        | FUNC(t2,_,_) -> 
          if t1 = t2 then (left_binary_type, (true,type_table))
          else (CONSTANT(CNone), (false, type_table))
        | CONSTANT(CInt(_)) ->
          begin
            match t1 with
            | CONSTANT(CInt(_)) -> (t1,(true,type_table))
            | _ -> (CONSTANT(CNone), (false, type_table))
          end
        | CONSTANT(CBool(_)) ->
          begin
            match t1 with
            | CONSTANT(CBool(_)) -> (t1,(true,type_table))
            | _ -> (CONSTANT(CNone), (false, type_table))
          end
        | CONSTANT(CString(_)) ->
          begin
            match t1 with
            | CONSTANT(CString(_)) -> (t1,(true,type_table))
            | _ -> (CONSTANT(CNone), (false, type_table))
          end
        | CFloat(b) ->
          begin
            match t1 with
            | CFloat(_)   
            | CONSTANT(CInt(_)) -> (CFloat(b),(true,type_table))
            | _ -> (CONSTANT(CNone), (false, type_table))
          end
        | ARRAY(_,_) ->
          begin
            match t1 with
            | ARRAY(_,_) -> (t1,(true,type_table))
            | _ -> (CONSTANT(CNone), (false, type_table))
          end
        | TYPE_IDF(_,_) -> 
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,t1) else (v,t)) type_table in
          (t1,(true,new_type_table))
        | CONSTANT(CNone) -> (CONSTANT(CNone),(true,type_table))

        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | ARRAY(_,_) ->
        begin
        match right_binary_type with
        | ARRAY(_,_) -> (left_binary_type, (true,type_table))
        | _ -> (CONSTANT(CNone), (false, type_table))
        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | CFloat(_) -> (CONSTANT(CNone),(true,type_table))
      | CONSTANT(CNone) -> (CONSTANT(CNone),(true,type_table))
      end
  | Compare (left, _, right) -> 
    let (left_binary_type,(no_error1,_)) = analyze_expr left type_table in
    let (right_binary_type,(no_error2,_)) = analyze_expr right type_table in
    if (no_error1 = false) || (no_error2 = false) then ((CONSTANT(CNone)),(false,type_table))
    else
      begin
      match left_binary_type with
      | CONSTANT(CInt(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CInt(_) -> (CONSTANT(CBool(true)),(true,type_table))
          | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | CFloat(_) -> (CONSTANT(CBool(true)),(true,type_table))
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        | FUNC(t,_,_) -> 
          begin
          match t with
          | CONSTANT(CInt(_)) -> (CONSTANT(CBool(true)),(true,type_table))
          | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | ARRAY(_,_) -> (CONSTANT(CBool(true)),(false,type_table))
        end
      | CONSTANT(CBool(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CBool(_) -> (CONSTANT(CBool(true)),(true,type_table))
          | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        | FUNC(t,_,_) ->
          begin
            match t with
            | CONSTANT(CBool(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | CFloat(_) 
        | ARRAY(_,_) -> (CONSTANT(CBool(true)),(false,type_table))
        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | CONSTANT(CString(_)) ->
        begin
        match right_binary_type with
        | CONSTANT(b) ->
          begin
          match b with
          | CString(_) -> (CONSTANT(CBool(true)),(true,type_table))
          | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | TYPE_IDF(_,(*n1*)_) ->
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,left_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        | FUNC(t,_,_) ->
          begin
            match t with
            | CONSTANT(CString(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)),(false,type_table))
          end
        | CFloat(_)
        | ARRAY(_,_) -> (CONSTANT(CBool(true)),(false,type_table))
        (*| CONSTANT(CNone) -> (true,type_table)*)
        end
      | TYPE_IDF(_,n1) ->
        begin
        match right_binary_type with
        | CONSTANT(_) -> 
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        | TYPE_IDF(_,n2) ->
          if n1 = n2 then (left_binary_type,(true,type_table))
          else 
            let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
            (CONSTANT(CBool(true)),(true,new_type_table))
        | FUNC(t,_,_) ->
            let new_type_table = List.map (fun (v,t1) -> if t1 = left_binary_type then (v,t) else (v,t1)) type_table in
            (CONSTANT(CBool(true)),(true,new_type_table))
        | ARRAY(_,_) ->
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        (*| CONSTANT(CNone) -> (true,type_table)*)
        | CFloat(_) ->
          let new_type_table = List.map (fun (v,t) -> if t = left_binary_type then (v,right_binary_type) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        end
      | FUNC(t1,_,_) ->
        begin
        match right_binary_type with
        | FUNC(t2,_,_) -> 
          if t1 = t2 then (CONSTANT(CBool(true)), (true,type_table))
          else (CONSTANT(CBool(true)), (false, type_table))
        | CONSTANT(CInt(_)) ->
          begin
            match t1 with
            | CONSTANT(CInt(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)), (false, type_table))
          end
        | CONSTANT(CBool(_)) ->
          begin
            match t1 with
            | CONSTANT(CBool(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)), (false, type_table))
          end
        | CONSTANT(CString(_)) ->
          begin
            match t1 with
            | CONSTANT(CString(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)), (false, type_table))
          end
        | CFloat(_) ->
          begin
            match t1 with
            | CFloat(_)   
            | CONSTANT(CInt(_)) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)), (false, type_table))
          end
        | ARRAY(_,_) ->
          begin
            match t1 with
            | ARRAY(_,_) -> (CONSTANT(CBool(true)),(true,type_table))
            | _ -> (CONSTANT(CBool(true)), (false, type_table))
          end
        | TYPE_IDF(_,_) -> 
          let new_type_table = List.map (fun (v,t) -> if t = right_binary_type then (v,t1) else (v,t)) type_table in
          (CONSTANT(CBool(true)),(true,new_type_table))
        | CONSTANT(CNone) -> (CONSTANT(CBool(true)),(true,type_table))

        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | ARRAY(_,_) ->
        begin
        match right_binary_type with
        | ARRAY(_,_) -> (CONSTANT(CBool(true)), (true,type_table))
        | _ -> (CONSTANT(CBool(true)), (false, type_table))
        end
        (*| CONSTANT(CNone) -> (true,type_table)*)
      | CFloat(_) -> (CONSTANT(CBool(true)),(true,type_table))
      | CONSTANT(CNone) -> (CONSTANT(CBool(true)),(true,type_table))
      end
  | BoolOp (_, _) -> (CONSTANT(CNone),(true,type_table))
  | List exprs 
  | Tuple exprs -> 
    let error_lst = List.map (fun x -> analyze_expr x type_table) exprs in
    let error_lst2 = List.map (fun (_, (no_error,_)) -> no_error) error_lst in
    if List.mem false error_lst2 then (CONSTANT(CNone),(false,type_table)) 
    else  (ARRAY("ARRAY",List.length exprs), (true,type_table))
  | Subscript (e1, e2) -> 
    let (e2_type,(no_error1,_)) = analyze_expr e2 type_table in
    let (e1_type,(no_error2,_)) = analyze_expr e1 type_table in
    if (no_error1 = false) || (no_error2 = false) then (CONSTANT(CNone),(false,type_table))
    else
      begin
      match e1_type with 
      | ARRAY(_,_) ->
        begin
        match e2_type with
        | CONSTANT(CInt(c)) ->
          begin
          match e1 with
          | Name x -> 
            (*let (array_idf, t) = find_if_exist x type_table in*)
            let var_to_find = x^"["^(string_of_int c)^"]" in
            let (_, s_type) = find_if_exist (var_to_find) (type_table) in
            (s_type,(true,type_table))
          | _ -> (CONSTANT(CNone),(false,type_table))
          end
        | _ -> (CONSTANT(CNone),(false,type_table))
        end
      | _ -> (CONSTANT(CNone),(false,type_table))
      end
  | Call (f, args) when is_the_int_function f && List.length args = 1 -> 
    let arg = List.nth args 0 in 
    let (_,(no_error,_)) = analyze_expr arg type_table in
    if no_error = false then (CONSTANT(CNone), (false,type_table))
    else (CONSTANT(CInt(1)),(true,type_table))
  | Call (f, args) when is_the_isinstance_function f && List.length args = 2 -> 
    let idf = (List.nth args 0) in
    let (_,(no_error,_)) = analyze_expr idf type_table in
    if no_error = false then (CONSTANT(CNone), (false,type_table))
    else (CONSTANT(CBool(true)),(true,type_table))
  | Call (f, []) when is_the_input_function f -> 
    (* input type 수정 필요!*)
    (CONSTANT(CString("input")),(true,type_table))
  | Call (f, args) when is_the_print_function f -> 
    let table_answer_lst = List.map (fun x -> analyze_expr_stmt x type_table) args in
    let table_answer_lst2 = List.map (get_first_from_type_table) table_answer_lst in
    if List.mem false table_answer_lst2 then (CONSTANT(CNone),(false,type_table))
    else
      (CONSTANT(CNone),(true,type_table))
  | Call (f, args) when is_the_len_function f && List.length args = 1 ->
    let arg = List.nth args 0 in 
    let (_,(no_error,_)) = analyze_expr arg type_table in
    if no_error = false then (CONSTANT(CNone), (false,type_table))
    else (CONSTANT(CInt(1)),(true,type_table))
  | Call (f, args) -> (* user-defined functions *)
    let (f_type,(no_error,_)) = analyze_expr f type_table in
    if no_error = false then (CONSTANT(CNone),(false,type_table)) 
    else
      begin
      match f_type with
      | FUNC(t,idfs,f_type_table) ->
        if ((List.length idfs) = (List.length args)) then 
          let error_lst = List.map (fun x -> analyze_expr x type_table) args in
          let error_lst2 = List.map (fun (_, (no_error,_)) -> no_error) error_lst in
          if List.mem false error_lst2 then (CONSTANT(CNone),(false,type_table)) 
          else 
            let filtered_f_type_table = List.find_all (fun (v,_) -> List.mem v idfs) f_type_table in
            let filtered_f_type_table2 = List.map (fun (_,t) -> t) filtered_f_type_table in
            let args_type_lst = List.map (fun (t,(_,_)) -> t) error_lst in
            let compared_result = List.map2 compare_type filtered_f_type_table2 args_type_lst in

            if List.mem false compared_result then (CONSTANT(CNone),(false,type_table)) 
            else
              (t,(true,type_table))
        else (CONSTANT(CNone),(false,type_table)) 
      | _ -> (CONSTANT(CNone),(false,type_table))
      end
  | ListComp (_, _) -> (CONSTANT(CNone),(false,type_table)) 
  | Lambda (_, _) -> (CONSTANT(CNone),(false,type_table)) 
  | IfExp(condition,true_expr,false_expr) -> 
    let (condition_type,(no_error1,_)) = analyze_expr condition type_table in
    let (_,(no_error2,_)) = analyze_expr true_expr type_table in
    let (_,(no_error3,_)) = analyze_expr false_expr type_table in
    if (no_error1 = false) || (no_error2 = false) || (no_error3 = false) then (CONSTANT(CNone),(false,type_table))
    else
      begin
      match condition_type with 
      | CONSTANT(CBool(_)) ->
        (CONSTANT(CString("Ifexpr!")), (true,type_table))
      | _ -> (CONSTANT(CNone),(false,type_table))
      end
  | _ -> (CONSTANT(CNone),(false,type_table)) 

and compare_type : t -> t -> bool = fun left right ->
  match left with
  | CONSTANT(CInt(_)) ->
    begin
      match right with
      | CONSTANT(b) ->
        begin
          match b with
          | CInt(_) -> true
          | _ -> false
        end
      | CFloat(_) 
      | TYPE_IDF(_,_) -> true
      | FUNC(t1,_,_) -> compare_type t1 left
      | _ -> false
    end
  | CONSTANT(CBool(_)) ->
    begin
      match right with
      | CONSTANT(b) ->
        begin
          match b with
          | CBool(_) -> true
          | _ -> false
        end
      | TYPE_IDF(_,_) -> true
      | FUNC(t1,_,_) -> compare_type t1 left
      | _ -> false
    end 
  | CONSTANT(CString(_)) ->
    begin
      match right with
      | CONSTANT(b) ->
        begin
          match b with
          | CString(_) -> true
          | _ -> false
        end
      | TYPE_IDF(_,_) -> true
      | _ -> false
    end 
  | ARRAY(_,_) ->
    begin
      match right with
      | ARRAY(_,_) -> true
      | FUNC(t1,_,_) -> compare_type t1 left
      | _ -> false
    end
  | FUNC(t1,_,_) -> compare_type t1 right
  | CFloat(_) ->
    begin
      match right with
      | CONSTANT(CInt(_))
      | CFloat(_) 
      | TYPE_IDF(_,_) -> true
      | FUNC(t1,_,_) -> compare_type t1 left
      | _ -> false
    end
  | CONSTANT(CNone) -> false
  | TYPE_IDF(_,_) -> true
and is_the_int_function expr = 
  match expr with
  | Name "int" -> true 
  | _ -> false

and is_the_isinstance_function expr = 
  match expr with
  | Name "isinstance" -> true 
  | _ -> false

and is_the_input_function expr = 
match expr with
| Name "input" -> true 
| _ -> false

and is_the_print_function expr = 
  match expr with
  | Name "print" -> true 
  | _ -> false
and is_the_len_function expr = 
  match expr with
  | Name "len" -> true 
  | _ -> false


