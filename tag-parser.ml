#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)
| ScmNil -> ScmConst(sexpr)
| ScmBoolean(x) -> ScmConst(sexpr)
| ScmChar(x) -> ScmConst(sexpr)
| ScmNumber(x) ->ScmConst(sexpr)
| ScmString(x) -> ScmConst(sexpr)
| ScmVector(x) -> ScmConst(sexpr)
| ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst(x)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit,ScmNil))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst(ScmVoid))
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| ScmPair(ScmSymbol("or"), x) -> parse_or x
| ScmPair(ScmSymbol("lambda"),ScmPair(ScmSymbol(x), body)) -> ScmLambdaOpt([], x, parse_seq body) 
| ScmPair(ScmSymbol("lambda"),ScmPair(params, body)) -> if scm_is_list params then ScmLambdaSimple(sexpr_to_string_list params, parse_seq body)
 else ScmLambdaOpt(without_last_string_list params, last_param params, parse_seq body)
| ScmPair(ScmSymbol("define"), ScmPair(ScmPair(var, args), body)) -> parse_define var (ScmPair(ScmSymbol("lambda"), ScmPair(args, body)))
| ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(value, ScmNil))) -> parse_define var value
| ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil))) -> parse_set var value
| ScmPair(ScmSymbol("begin"), exprs) -> parse_begin exprs
| ScmPair(a,b) -> parse_app a b
| ScmSymbol(x) -> if List.mem x reserved_word_list then raise (X_reserved_word (x)) else ScmVar(x)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))


and parse_begin exprs =
match exprs with
| ScmPair(a, ScmNil) -> tag_parse_expression a
| ScmPair(a,b) ->  ScmSeq(sexpr_to_expr_list exprs)
| _ -> ScmConst(ScmNil)

and parse_app a b =
match a with
(* | ScmSymbol(x) -> if List.mem x reserved_word_list then raise (X_reserved_word (x)) else ScmApplic(tag_parse_expression a, sexpr_to_expr_list b) *)
| _ ->  ScmApplic(tag_parse_expression a, sexpr_to_expr_list b)

and parse_define var value =
let x = tag_parse_expression var in
match x with
| ScmVar(y) -> ScmDef(x, tag_parse_expression value)
| _ -> raise (X_syntax_error (ScmPair(ScmSymbol("define"), ScmPair(var, value)), "Expected variable on LHS of define"))

and parse_set var value =
let x = tag_parse_expression var in
match x with
| ScmVar(y) -> ScmSet(x, tag_parse_expression value)
| _ -> raise (X_syntax_error (ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil))), "Expected variable on LHS of set!"))
 
and parse_or sexpr =
match sexpr with
| ScmNil -> ScmConst(ScmBoolean(false))
| ScmPair(a, ScmNil) -> tag_parse_expression a
| ScmPair(a,b) -> ScmOr(tag_parse_expression a :: sexpr_to_expr_list b)
| _ -> ScmConst(ScmNil)

and sexpr_to_expr_list pair =
match pair with
| ScmNil -> []
| ScmPair(a,b) -> tag_parse_expression a :: sexpr_to_expr_list b
| _ -> [tag_parse_expression pair]

and parse_seq sexpr =
match sexpr with
| ScmPair(a, ScmNil) -> tag_parse_expression a
| ScmPair(a,b) -> ScmSeq(sexpr_to_expr_list sexpr)
| _ -> ScmConst(ScmNil)

and sexpr_to_string_list sexpr =
match sexpr with
| ScmPair(ScmSymbol(x),ScmNil) -> [x]
| ScmPair(ScmSymbol(x), b) -> x :: sexpr_to_string_list b
| _ -> []

and parse_and sexpr = 
match sexpr with
| ScmNil -> ScmBoolean true
| ScmPair(x, ScmNil) -> x
| ScmPair(x,y) -> ScmPair(ScmSymbol("if"), ScmPair(x, ScmPair(parse_and y, ScmPair(ScmBoolean false, ScmNil))))
| _ -> ScmNil

and parse_let pairs exprs =
let args =  build_args pairs in
let params = build_params pairs in
ScmPair(ScmPair(ScmSymbol("lambda"),(ScmPair(args, exprs))), params)


and last_param params =
match params with
| ScmPair(a,b) -> last_param b
| ScmSymbol(a) -> a
| _ -> ""

and without_last_string_list params = 
match params with
| ScmPair(ScmSymbol(x),ScmSymbol(y)) -> [x]
| ScmPair(ScmSymbol(x), b) -> x :: without_last_string_list b
| _ -> []

and build_args args =
 match args with
 | ScmNil -> ScmNil
 | ScmPair(a,b) -> 
  match a with
  | ScmPair(arg,ScmPair(exp, ScmNil)) -> ScmPair(arg, build_args b)
  | _ -> ScmNil

 and build_params params =
 match params with
 | ScmNil -> ScmNil
 | ScmPair(a,b) -> 
  match a with
  | ScmPair(arg,ScmPair(exp, ScmNil)) -> ScmPair(exp, build_params b)
  | _ -> ScmNil




and parse_cond ribs =
match ribs with
| ScmPair(ScmPair(ScmSymbol("else"), exprs), rest_ribs) -> ScmPair(ScmSymbol("begin"), exprs)
| ScmPair(ScmPair(expr, ScmPair(ScmSymbol("=>"), ScmPair(exprf, ScmNil))), rest_ribs) ->
let arg1 = ScmSymbol("value") in
(* let exp1 = expr in *)
let exp1 =  expr in
let arg2 = ScmSymbol("f") in
let exp2 = ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil, (ScmPair( exprf, ScmNil)))) in
(* let exp2 = ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil, exprf)) in *)
let arg3 = ScmSymbol("rest") in
let exp3 = ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil, ScmPair(parse_cond (rest_ribs), ScmNil))) in
let pairs = ScmPair(ScmPair(arg1,ScmPair(exp1, ScmNil)), ScmPair(ScmPair(arg2,ScmPair(exp2, ScmNil)), ScmPair(ScmPair(arg3,ScmPair(exp3, ScmNil)), ScmNil))) in
(* let test =  ScmPair (ScmSymbol "value", ScmNil) in *)
let test = ScmSymbol("value") in
let dit = ScmPair(ScmPair(ScmSymbol("f"), ScmNil), ScmPair(ScmSymbol("value"), ScmNil)) in
let dif =  ScmPair(ScmSymbol("rest"), ScmNil) in
let body = ScmPair(ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))), ScmNil) in
macro_expand(ScmPair(ScmSymbol("let"), ScmPair(pairs, body)))
| ScmPair(ScmPair(test, exprs), ScmNil) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), exprs),ScmNil)))
| ScmPair(ScmPair(test, exprs), rest_ribs) -> ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), exprs), ScmPair(parse_cond rest_ribs, ScmNil))))
| _ -> ScmNil


and parse_quasi expr =
match expr with
| (ScmPair(ScmSymbol "unquote", ScmPair (x, ScmNil))) -> x
(* bug *)
| ScmPair(ScmSymbol("unquote-splicing"),  ScmPair (x, ScmNil)) -> ScmPair(ScmSymbol "quote", ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(x, ScmNil)) , ScmNil))
| ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(x, ScmNil)), b) -> ScmPair(ScmSymbol("append"), ScmPair(x, ScmPair(parse_quasi b, ScmNil)))
| ScmSymbol(x) -> (ScmPair(ScmSymbol "quote", ScmPair (expr, ScmNil)))
| ScmNil -> (ScmPair(ScmSymbol "quote", ScmPair (expr, ScmNil)))
| ScmVector(x) -> let list_to_vector = ScmPair(ScmSymbol("list->vector"),ScmNil) in
                  let scheme_list = list_to_proper_list x in
                  let scheme_list = parse_quasi scheme_list in
                  let scheme_list = scm_append list_to_vector (ScmPair(scheme_list, ScmNil)) in scheme_list
| ScmPair(a,b) -> ScmPair(ScmSymbol("cons"),ScmPair(parse_quasi a, ScmPair(parse_quasi b, ScmNil)))
| _ -> expr

and vector_to_list x =
match x with
| a::b -> ScmPair(a, (vector_to_list b))
| a -> ScmNil

and build_whatever pairs =
 match pairs with
 | ScmPair(ScmPair(ScmSymbol(x),a),b) -> ScmPair(ScmPair(ScmSymbol(x), ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil)), (build_whatever b))
 | _ -> ScmNil

and build_set pairs exprs = 
 match pairs with
 | ScmPair(ScmPair(ScmSymbol(x),a),b) -> ScmPair(ScmPair(ScmSymbol("set!"), ScmPair(ScmSymbol(x), a)), (build_set b exprs))
 (* | _ ->  ScmPair(ScmPair(ScmSymbol("let"), ScmPair(ScmNil,exprs)), ScmNil) *)
 | _ ->  exprs


and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("and"), x) -> parse_and x
| ScmPair(ScmSymbol("let"), ScmPair(pairs, exprs)) ->  parse_let pairs exprs 
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(pair, ScmNil), exprs)) -> macro_expand(ScmPair(ScmSymbol("let"), ScmPair(ScmPair(pair,ScmNil), exprs)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(first_pair, rest_pairs), exprs)) ->
 macro_expand( ScmPair(ScmSymbol("let"), ScmPair(ScmPair(first_pair, ScmNil),ScmPair(ScmPair(ScmSymbol("let*"), ScmPair(rest_pairs, exprs)),ScmNil))))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil, exprs)) -> macro_expand(ScmPair(ScmSymbol("let"), ScmPair(ScmNil, exprs)))
| ScmPair(ScmSymbol("letrec"), ScmPair(pairs, exprs)) -> 
let whatever_pairs = build_whatever pairs in
let body = build_set pairs exprs in
macro_expand(ScmPair(ScmSymbol("let"), ScmPair(whatever_pairs, body)))
| ScmPair(ScmSymbol("cond"), ribs) -> parse_cond ribs
| ScmPair(ScmSymbol("quasiquote"), ScmPair(expr, ScmNil)) -> parse_quasi expr
| _ -> sexpr
end;; 

