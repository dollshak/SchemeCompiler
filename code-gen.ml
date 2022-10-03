#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;

  let primitive_names_to_labels =
 [
  (* Type queries  *)
  "boolean?"; "flonum?"; "rational?";
  "pair?"; "null?"; "char?"; "string?";
  "procedure?"; "symbol?";
  (* String procedures *)
  "string-length"; "string-ref"; "string-set!";
  "make-string"; "symbol->string";
  (* Type conversions *)
  "char->integer"; "integer->char"; "exact->inexact";
  (* Identity test *)
  "eq?";
  (* Arithmetic ops *)
  "+";"*"; "/"; "="; "<";
  (* Additional rational numebr ops *)
  "numerator"; "denominator"; "gcd";
  (* you can add yours here *)
  "apply" ; "car" ; "cdr" ; "cons" ; "set-car!" ; "set-cdr!"
  ]

 (* make_consts_tbl help funtions *)

 let rec findConstsInExpr expr = 
    match expr with
    | ScmConst'(x) -> [x]
    | ScmVar'(x) -> []
    | ScmBox'(var) -> []
    | ScmBoxGet'(var) -> []
    | ScmBoxSet'(var, expr) -> findConstsInExpr expr
    | ScmIf'(test,dit,dif) -> (findConstsInExpr test) @ (findConstsInExpr dit)@ (findConstsInExpr dif)
    | ScmSeq'(list) -> List.fold_left (List.append) [] (List.map (fun x -> findConstsInExpr x) list)
    | ScmOr'(list) -> List.fold_left (List.append) [] (List.map (fun x -> findConstsInExpr x) list)
    | ScmDef'(var,value) -> findConstsInExpr value
    | ScmSet'(var,value) -> findConstsInExpr value
    | ScmLambdaSimple'(args, body) -> findConstsInExpr body
    | ScmLambdaOpt'(args, rest_args, body) -> findConstsInExpr body
    | ScmApplic'(f,args) ->  List.fold_left (List.append) (findConstsInExpr f) (List.map (fun x -> findConstsInExpr x) args)
    | ScmApplicTP'(f, args) ->  List.fold_left (List.append) (findConstsInExpr f) (List.map (fun x -> findConstsInExpr x) args)

  let rec expandExprHelp expr = 
  match expr with
    | ScmVoid -> [expr]
    | ScmNil -> [expr]
    | ScmBoolean(_) -> [expr]
    | ScmChar(ch) -> [expr]
    | ScmString(str) -> [expr]
    | ScmSymbol(str) -> [ScmString(str)]
    | ScmNumber(num) -> [expr]
    | ScmVector(list) -> List.fold_left (List.append) [] (List.map (fun x -> expandExprHelp x) list)
    | ScmPair(first, rest) -> expandExprHelp first @ [first] @ expandExprHelp rest @ [rest]


  let rec expandExpr expr = 
  match expr with
    | ScmVoid -> []
    | ScmNil -> []
    | ScmBoolean(_) -> []
    | ScmChar(ch) -> []
    | ScmString(str) -> []
    | ScmSymbol(str) -> [ScmString(str)]
    | ScmNumber(num) -> []
    | ScmVector(list) -> expandExprHelp expr
    | ScmPair(first, rest) -> expandExprHelp expr
    

  let rec constMem x list = 
    match list with 
      |[] -> false
      |first::rest -> sexpr_eq first x || constMem x rest


  let rec listToSet list = 
    match list with 
      |[] -> []
      |first::rest -> if constMem first rest then listToSet rest else first :: listToSet rest


  let getSizeOfSob sexpr = 
    match sexpr with 
    | ScmVoid -> 1
    | ScmNil-> 1
    | ScmBoolean(_)-> 2
    | ScmChar(ch)-> 2
    | ScmString(str)-> String.length str +9
    | ScmSymbol(str)->  9
    | ScmNumber(ScmReal(x)) -> 9
    | ScmNumber(ScmRational(x,y)) -> 17
    | ScmVector(sexprs) -> 1 + (List.length sexprs * 8) + 8
    | ScmPair(car, vdr)-> 17

  let rec getIndexOfConst sexp constTable = 
    match constTable with
    |[] -> -1 
    |(const, (offset, _))::rest -> if sexpr_eq const sexp then offset else getIndexOfConst sexp rest 



  let rec getIndexOfFvar fvarsTable var = 
    match fvarsTable with
    | [] -> -1 
    | (var_name, offset) :: rest -> if var = var_name then offset else getIndexOfFvar rest var  


  let getString sexpr constTable =
      match sexpr with 
      | ScmVoid -> "db T_VOID"
      | ScmNil-> "db T_NIL"
      | ScmBoolean(bool)-> if bool==true then "db T_BOOL, 1" else "db T_BOOL, 0"
      | ScmChar(ch)-> "MAKE_LITERAL_CHAR(" ^ (string_of_int(int_of_char ch)) ^ ")"
      (* | ScmChar(ch)-> "MAKE_LITERAL_CHAR("^"\""^(String.make 1 ch)^"\""^")" *)
      | ScmString(str)-> "MAKE_LITERAL_STRING "^"\""^str^"\""
      | ScmSymbol(str)-> let off = getIndexOfConst (ScmString(str)) constTable in let strOff = string_of_int off in "MAKE_LITERAL_SYMBOL(const_tbl+"^ strOff ^")"
      | ScmNumber(ScmRational (x, y))-> "MAKE_LITERAL_RATIONAL("^(string_of_int x)^","^(string_of_int y)^")"
      | ScmNumber(ScmReal(x)) -> "MAKE_LITERAL_REAL("^(string_of_float x)^")"
      | ScmPair(car, cdr)-> "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (getIndexOfConst car constTable))^", const_tbl+"^(string_of_int (getIndexOfConst cdr constTable))^")"
      | ScmVector(sexprs) -> let pointersOfSexpers = List.fold_left (^) ("") (List.map (fun x -> (" const_tbl+"^(string_of_int (getIndexOfConst x constTable)) ^", " )) sexprs) in
                             "MAKE_LITERAL_VECTOR "^pointersOfSexpers^""

  let rec insertStrings constTable currConstTable = 
  match currConstTable with
  |[] -> []
  |(const, (offset, _))::rest -> [(const, (offset, (getString const constTable)))] @ insertStrings constTable rest
    
  let rec generateConstTable list currOffset = 
    match list with 
      |[] -> []
      |first::rest -> [(first, (currOffset, ""))] @ (generateConstTable rest (currOffset+(getSizeOfSob first)))
      
  let rev l =
      List.fold_left (fun a e -> e :: a) [] l

  (* make_fvars_tbl help funtions *)

  let addVarIfFree var = 
    match var with 
      |VarFree(str) -> [str]
      |VarParam(str, i) -> []
      |VarBound(str, i, j) -> []

  let rec findFvars expr = 
    match expr with
    | ScmConst'(x) -> []
    | ScmVar'(var) -> addVarIfFree var
    | ScmBox'(var) -> addVarIfFree var
    | ScmBoxGet'(var) -> addVarIfFree var
    | ScmBoxSet'(var, expr) -> addVarIfFree var
    | ScmIf'(test,dit,dif) -> (findFvars test) @ (findFvars dit)@ (findFvars dif)
    | ScmSeq'(list) -> List.fold_left (List.append) [] (List.map (fun x -> findFvars x) list)
    | ScmOr'(list) -> List.fold_left (List.append) [] (List.map (fun x -> findFvars x) list)
    | ScmDef'(var,value) -> (addVarIfFree var) @ (findFvars value)
    | ScmSet'(var,value) -> (addVarIfFree var) @ (findFvars value)
    | ScmLambdaSimple'(args, body) ->  findFvars body
    | ScmLambdaOpt'(args, rest_args, body) -> findFvars body
    | ScmApplic'(f,args) ->  List.fold_left (List.append) (findFvars f) (List.map (fun x -> findFvars x) args)
    | ScmApplicTP'(f, args) ->  List.fold_left (List.append) (findFvars f) (List.map (fun x -> findFvars x) args)


  let rec insertIndexes list index = 
    match list with 
    |[] -> []
    |first::rest -> (first , index):: (insertIndexes rest (index+8))


  let rec strListToSet list = 
    match list with 
      |[] -> []
      |first::rest -> if List.mem first rest then strListToSet rest else first :: strListToSet rest

  let make_consts_tbl asts = 
    let constsList = List.fold_left (List.append) [] (List.map (fun expr -> findConstsInExpr expr) asts) in
    let constsSet = listToSet constsList in 
    let subconstsList = List.fold_left (List.append) [] (List.map (fun expr -> expandExpr expr) constsSet) in
    let constsAndSubconstsList = subconstsList @ constsSet in
    let defaultSexps = [ScmVoid ; ScmNil ; ScmBoolean (false) ; ScmBoolean (true)] in
    let allConsts =  rev (listToSet (rev (defaultSexps @ constsAndSubconstsList))) in
    let constTable = generateConstTable allConsts 0 in
    let constTablewithStrings = insertStrings constTable constTable in 
    constTablewithStrings

  let make_fvars_tbl asts = 
    (* let libraryFuns = List.fold_left (List.append) [] (List.map (fun a, b -> a) primitive_names_to_labels) in *)
    let libraryFuns = primitive_names_to_labels in
    let freeVars = List.fold_left (List.append) [] (List.map (fun expr -> findFvars expr) asts) in
    let freeVarsAndLib = libraryFuns @ freeVars in
    let freeVarsSet = rev (strListToSet  (rev freeVarsAndLib)) in
    let fravsTable = insertIndexes freeVarsSet 0 in
    fravsTable


  (*generate methods *)
  let counter = ref 0;;
  let get_counter = (fun () -> counter := (!counter +1); (string_of_int !counter));;



  let rec generate_help consts fvars e env_size =
	match e with
	| ScmConst'(c) -> generate_const consts fvars c
	| ScmVar'(VarBound(_,major,minor)) -> generate_var_bound_get major minor
	| ScmVar'(VarFree(v)) -> generate_var_free_get fvars v
	| ScmVar'(VarParam(_,minor)) -> generate_var_param_get minor
	| ScmSet'(VarParam(_,minor),expr) -> generate_var_param_set env_size consts fvars minor expr
	| ScmSet'(VarFree(v),expr) -> generate_var_free_set env_size consts fvars v expr
	| ScmSet'(VarBound(_,major,minor),expr) -> generate_var_bound_set env_size consts fvars major minor expr
	| ScmIf'(test, dit, dif) -> generate_if env_size consts fvars test dit dif
	| ScmDef'(VarFree(var), expr) -> generate_def env_size consts fvars var expr
	| ScmOr'(list) -> 	let index = get_counter() in generate_or env_size consts fvars list index
	| ScmSeq'(list) -> generate_seq env_size consts fvars list
	| ScmBoxGet'(var) -> generate_box_get env_size consts fvars var 
	| ScmBoxSet'(var,expr) -> generate_box_set env_size consts fvars var expr 
	| ScmBox'(var) -> generate_box env_size consts fvars var 
	| ScmLambdaSimple'(args, body) -> generate_lambda_simple env_size consts fvars args body
	| ScmLambdaOpt'(args, opt, body) -> let new_args = args@[opt] in generate_lambda_opt (env_size + 1) consts fvars new_args body
	| ScmApplic'(proc, args) -> generate_app env_size consts fvars proc args
	| ScmApplicTP'(proc, args) -> generate_app_TP env_size consts fvars proc args
	| _ -> ""

and generate_const consts fvars c = 
	"mov rax, const_tbl + " ^ string_of_int (getIndexOfConst c consts) ^ "
	"

and generate_var_bound_get major minor = 
	"mov rax, qword [rbp + 8 * 2]
	mov rax, qword [rax + 8 * " ^ string_of_int major ^ "] 
	mov rax, qword [rax + 8 *" ^ string_of_int minor ^ "]
	"

and generate_var_bound_set env_size consts fvars major minor expr = 
	let gen_expr = generate_help consts fvars expr env_size in
	gen_expr ^ "
	mov rbx, qword [rbp + 8 * 2]
	mov rbx, qword [rbx + 8 * " ^ string_of_int major ^ "]
	mov qword [rbx + 8 * " ^ string_of_int minor ^ "], rax
	mov rax, SOB_VOID_ADDRESS
	"

and generate_var_param_get minor =
	 "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int minor ^")]
	 "

and generate_var_param_set env_size consts fvars minor expr = 
	let gen_expr = generate_help consts fvars expr env_size in
	gen_expr ^ "
	mov qword [rbp + 8 * (4 + " ^ string_of_int minor ^ ")], rax
	mov rax, SOB_VOID_ADDRESS
	"

and generate_var_free_get fvars var =
let offset =  getIndexOfFvar fvars var in
	"mov rax, qword [fvar_tbl + " ^ string_of_int (offset)  ^ "]
	"

and generate_var_free_set env_size consts fvars var expr = 
	let gen_expr = generate_help consts fvars expr env_size in
	gen_expr ^ "
	mov qword [fvar_tbl + " ^ string_of_int (getIndexOfFvar fvars var) ^"], rax
	mov rax, SOB_VOID_ADDRESS
	"

and generate_if env_size consts fvars test dit dif = 
	let gen_test = generate_help consts fvars test env_size in
	let gen_dit = generate_help consts fvars dit env_size in
	let gen_dif = generate_help consts fvars dif env_size in
	let index = get_counter() in
	gen_test ^ "
  cmp rax, SOB_FALSE_ADDRESS
	je Lelse" ^ index ^ "
  " ^ gen_dit ^
	"jmp Lexit" ^ index ^ "
	Lelse" ^ index ^ ":
	" ^ gen_dif ^ "
	Lexit" ^ index ^ ":
	"

and generate_or env_size consts fvars list index =
	let or_code expr =  generate_help consts fvars expr env_size ^ "
	 cmp rax, SOB_FALSE_ADDRESS
	 jne Lexit" ^ index ^ "\n" in

	match list with
	 | first :: [] -> (generate_help consts fvars first env_size) ^ "
		Lexit"  ^ index ^ ":
		"
	 | first :: rest -> (or_code first) ^ (generate_or env_size consts fvars rest index)
   | _ -> ""


and generate_seq env_size consts fvars list =
	 List.fold_left (fun accumaltor expr -> accumaltor ^ (generate_help consts fvars expr env_size)) "\n" list

and generate_box_get env_size consts fvars var =
	let gen_expr = generate_help consts fvars (ScmVar' var) env_size in
	gen_expr ^ "
	mov rax, qword [rax]
	"

and generate_box_set env_size consts fvars var expr =
	let gen_expr = generate_help consts fvars expr env_size in
	let gen_var = generate_help consts fvars (ScmVar' var) env_size in
	gen_expr ^ "
	push rax
	" ^ gen_var ^ "
	pop qword [rax] 
	mov rax, SOB_VOID_ADDRESS
	"



and generate_lambda_simple env_size consts fvars arg_list body =
	let index = get_counter() in
	let gen_body = generate_help consts fvars body (env_size +1) in
	let env_code = get_blue_code env_size index in
	let closure_body = "
	Lcode" ^ index ^ ":
	push rbp
	mov rbp, rsp
	" ^ gen_body ^ "
	leave
	ret
	Lcont" ^ index ^ ":
	" in 
	env_code ^ closure_body


and get_fix_stack_code index new_n = 
 "
mov r8, qword [rsp + 16] ;; r8 -> old n
mov r9, " ^ new_n ^ " ;; -> r9 -> new n
cmp r8, r9
je fix_case_3_" ^ index ^ "
jl fix_case_2_" ^ index ^ "


;; case 1 :
;;if new_n > old_n
;; make args be a improper list
	fix_case_1_" ^ index ^ ":
	;; diff = new_n - old_n
	;; acc = SOB_NIL_ADDRESS
	;; while counter <= diff
	;; 		acc = make_pair(last_element, acc)
	;; 		last_element = acc
	;; 		counter ++
	;; counter = 0
	;; while counter <= diff
	;; 		last_element = null
	;; n = old_n
	
mov rbx, r8
inc rbx
sub rbx, r9 ;; rbx -> diff
mov rax, rbx ;; rax -> save diff
mov rdx, SOB_NIL_ADDRESS ;; rdx -> list
make_pair_loop" ^ index ^ ":
mov rcx , r9
add rcx , rbx
inc rcx
mov r14, qword [rsp + 8*(rcx)] ;; r14 -> last argument
MAKE_PAIR(r15, r14, rdx) ;; r15 -> pair(last_element, acc)
mov rdx, r15 ;; rdx -> list
dec rbx
jnz make_pair_loop" ^ index ^ "
mov qword [rsp + 8 * (2 + " ^ (new_n) ^ ")], rdx ;; put the list in the stack
mov r10, r9
add r10, 3 ;; r10 -> the size of new stack -1
mov r11, r8
add r11, 3 ;; r11 -> the size of old stack -1
shift_up_loop" ^ index ^ ":
dec r11
dec r10
mov r12, qword [rsp+8*r10]
mov qword [rsp+8*r11], r12
jnz shift_up_loop" ^ index ^ "

fix_rsp" ^ index ^ ":
cmp r11, 0
je end_fix_rsp" ^ index ^ "
add rsp, 8
dec r11
jmp fix_rsp" ^ index ^ "
end_fix_rsp" ^ index ^ ":
mov qword [rsp + 16], r9
jmp end_fix" ^ index ^ "

  ;; case 3 :
;; old_n = new_n
	fix_case_3_" ^ index ^ ":
	mov r10, qword [rsp + 8*(2+r8)] ;; r10 -> last arg
	MAKE_PAIR(r11, r10, SOB_NIL_ADDRESS) ;;-> r11 -> pointer to pair
	mov qword [rsp + 8*(2+r8)], r11 ;;  last arg become pair
	jmp end_fix" ^ index ^ "


;; case 2 :
;;if new_n < old_n 

fix_case_2_" ^ index ^ ":
	sub rsp, 8
	mov r10, r9
	add r10, 3 ;; r10 -> new stack size
	mov r11, r8 
	add r11, 3 ;; r11 -> old stack size
	mov r12, 0 ;; r12 -> counter
	shift_down_loop" ^ index ^ ":
	cmp r11, 0
	je end_shift_down_loop" ^ index ^ "
	mov r13, qword [rsp + 8*(1 + r12)]
	mov qword [rsp + 8*r12], r13
	dec r11
	inc r12
	jmp shift_down_loop" ^ index ^"
	end_shift_down_loop" ^ index ^ ":
	mov qword [rsp + 16] , r9 ;; n = n + 1
	mov qword [rsp + 8*(r10-1)] , SOB_NIL_ADDRESS 

end_fix" ^ index ^ ":"


and get_blue_code env_size index = 
	if env_size == 0 then "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode" ^ index ^ ")
		jmp Lcont" ^ index ^ "\n" 
                  else "
                      ;; CREATE EXT_ENV
                        MALLOC r8, " ^ (string_of_int (8*(env_size + 1))) ^ "
                        mov qword r9, [rbp+16] ;; r9 -> current env
                        mov r12, " ^ (string_of_int env_size) ^"
                        mov r13, qword [rbp+24] ;; r13-> n 
                        mov rbx, 0 ; -> counter i
                        mov rcx, 1 ; -> counter j
                        copy_params" ^ index ^ ":
                        cmp rbx, r12
                        je end_copy_params" ^ index ^ "
                        mov r10, qword [r9 + 8*rbx] ; r10 -> curr_env[i]
                        mov qword [r8 + 8*rcx], r10 ;; ext_env[j] = curr_env[i]
                        inc rbx
                        inc rcx
                        jmp copy_params" ^ index ^ "
                        end_copy_params" ^ index ^ ":
                        mov rdx, r13
                        shl rdx, 3
                        ;; ALLOCATE CLOSURE OBJECT
                        MALLOC r15, rdx ;; malloc 8*n
                        mov r14, 0 ;; r14 -> counter of args in new env
                        copy_stack_args" ^ index ^ ":
                        cmp r14, r13
                        je end_copy_stack_args" ^ index ^ "
                        mov rbx, qword [rbp + 8*(4+r14)] ;; rbx = param_i
                        mov qword [r15 + 8*r14] , rbx;; ext_env[0][i]
                        inc r14
                        jmp copy_stack_args" ^ index ^ "
                        end_copy_stack_args" ^ index ^ ":
                        mov qword [r8], r15 ;; ext_env[0] = new_env
                        ;; MAKE_CLOSURE
                        MAKE_CLOSURE(rax,r8, Lcode" ^ index ^ ")
                        jmp Lcont" ^ index ^"
                        "
	
	
	


and generate_lambda_opt env_size consts fvars arg_list body =
	let index = get_counter() in
	let gen_body = generate_help consts fvars body (env_size+1) in
	let env_code = get_blue_code env_size index in
	let fix_stack_code = get_fix_stack_code index (string_of_int (List.length arg_list)) in 
	let orange_code = "Lcode" ^ index ^ ":" ^
	fix_stack_code ^ "
	push rbp
	mov rbp, rsp
	" ^ gen_body ^ "
	leave
	ret
	Lcont" ^ index ^ ":
	" in
	env_code ^ orange_code

and generate_app env_size consts fvars proc args = 
  let gen_args = List.fold_right (fun e acc -> acc^(generate_help consts fvars e env_size)^"push rax\n") args "\n" in
  let n = string_of_int (List.length args) in
  let gen_proc = generate_help consts fvars proc env_size in
  gen_args^"
  push "^n^"
  "^gen_proc^"
  push qword[rax + 1]
  call qword[rax + 9]
  add rsp, 8 ;;pop env
  pop rbx
  lea rsp , [rsp + 8*rbx]
  "


and generate_app_TP env_size consts fvars proc args =	
  let gen_args = List.fold_right (fun e acc -> acc^(generate_help consts fvars e env_size)^"\n push rax \n") args "\n" in
  let gen_proc = generate_help consts fvars proc env_size in
		 gen_args ^ "
     push " ^  string_of_int (List.length args) ^ "
		 " ^ gen_proc ^ "
		push qword [rax + 1]
		push qword [rbp + 8]
		push qword [rbp]
		mov r8, qword [rbp + 24]
		add r8, 4
		shl r8, 3
		SHIFT_FRAME " ^ string_of_int ((List.length args) + 4) ^ "
		add rsp, r8
		pop rbp
		jmp qword [rax  + 9]
		"

and generate_def env_size consts fvars var expr = 
	let gen_exp = generate_help consts fvars expr env_size in
	gen_exp ^ "
	mov qword [fvar_tbl + " ^ string_of_int (getIndexOfFvar fvars var) ^ "], rax
	mov rax, SOB_VOID_ADDRESS
	"
and generate_box env_size consts fvars var = 
	let gen_exp = generate_help consts fvars (ScmVar' var) env_size in
	gen_exp ^ "
	MALLOC rbx, 8
	mov [rbx], rax
	mov rax, rbx
	"

let generate consts fvars e = 
	generate_help consts fvars e (0)
	(* generate_help consts fvars e (-1) *)



end;;

