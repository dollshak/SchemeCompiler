(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
    match pe with
      | ScmConst(x) -> ScmConst'(x) 
      | ScmVar(name) -> ScmVar'(tag_lexical_address_for_var name params env) 
      | ScmIf(test,dit,dif) -> ScmIf'(run test params env, run dit params env, run dif params env)
      | ScmSeq(list)  -> ScmSeq'(List.map (fun x -> run x params env) list)
      | ScmOr(list) -> ScmOr' (List.map (fun x -> run x params env) list)
      | ScmSet(ScmVar(name),value) -> ScmSet'(tag_lexical_address_for_var name params env, run value params env)
      | ScmDef(ScmVar(name),value) -> ScmDef'(tag_lexical_address_for_var name params env, run value params env)
      | ScmLambdaSimple(args, body) -> ScmLambdaSimple'(args, run body args (params :: env))
      | ScmLambdaOpt(args, rest_args, body) -> ScmLambdaOpt'(args, rest_args, run body (args@[rest_args]) (params::env))
      (* | ScmLambdaOpt(args, rest_args, body) -> let new_params = params @ [rest_args] in ScmLambdaOpt'(args, rest_args, run body (new_params) (extend_env env new_params)) *)
      | ScmApplic(f, args) -> ScmApplic'((run f params env),List.map (fun x -> run x params env) args)
      | _ -> raise X_this_should_not_happen


   in 
   run pe [] [];;


  let without_last_elemnt list =
    List.rev (List.tl (List.rev list))

  let last_element list = 
  List.hd (List.rev list)

  let rec find_index name args index = 
  match args with
  | first :: rest -> if first = name then index else find_index name rest (index+1)
  | [] -> raise X_this_should_not_happen 


let help element write_list =
    let new_list = List.filter (fun x -> x != element) write_list in


  match new_list with
  | [] -> false
  | _ -> true

  let rec check_share_rib read_list write_list = 
      let bool_list = List.map (fun x -> help x write_list) read_list in
      List.mem true bool_list

  let rec replace_body body_expr var_should_box =
    match body_expr with
      | ScmIf'(test,dit,dif) -> ScmIf'(replace_body test var_should_box ,replace_body dit var_should_box ,replace_body dif var_should_box )
      | ScmSeq'(list) -> ScmSeq'(List.map (fun x -> replace_body x var_should_box ) list)
      | ScmOr'(list) -> ScmOr'(List.map (fun x -> replace_body x var_should_box ) list)
      | ScmDef'(var,value) -> ScmDef'(var, replace_body value var_should_box )
      | ScmApplic'(f,args) -> ScmApplic'(replace_body f var_should_box , List.map (fun x -> replace_body x var_should_box ) args)
      | ScmApplicTP'(f , args) -> ScmApplicTP'(replace_body f var_should_box , List.map (fun x -> replace_body x var_should_box ) args)
      | ScmLambdaSimple'(args, body) -> if List.mem var_should_box args then body_expr else ScmLambdaSimple'(args, replace_body body var_should_box)
      | ScmLambdaOpt'(args, rest_args, body) -> let united_args = args @ [rest_args] in if List.mem var_should_box united_args then body_expr else ScmLambdaOpt'(args,rest_args, replace_body body var_should_box)
      | ScmSet'(VarBound(name,major,minor),value) ->if name = var_should_box then ScmBoxSet'(VarBound(name,major,minor), replace_body value var_should_box) else ScmSet'(VarBound(name,major,minor),replace_body value var_should_box)
      | ScmSet'(VarParam(name, place),value) -> if name = var_should_box then ScmBoxSet'(VarParam(name, place), replace_body value var_should_box) else ScmSet'(VarParam(name, place),replace_body value var_should_box) 
      | ScmSet'(var,value) -> ScmSet'(var, replace_body value var_should_box)
      | ScmVar'(VarParam(name, place)) ->  if name = var_should_box then ScmBoxGet'(VarParam(name, place)) else body_expr
      | ScmVar'(VarBound(name,major,minor)) -> if name = var_should_box then ScmBoxGet'(VarBound(name,major,minor)) else body_expr
      | ScmVar'(x) -> body_expr
      | _ -> body_expr

    and add_set_statment name index body_expr = 
      let temp = VarParam(name, index) in
      let statment = [ScmSet'(temp, ScmBox'(temp))] in
      match body_expr with
      | ScmSeq'(seq) -> ScmSeq'(statment@seq)
      | _ -> ScmSeq'(statment@[body_expr])
  
    and new_body body_expr vars_should_box args =
      match vars_should_box with
      | [] -> body_expr
      | var :: rest -> let index = find_index var args 0 in new_body (add_set_statment var index (replace_body body_expr var)) rest args


    let this_var_should_box arg expr body =
      let rec writes arg expr enclosing_lambda is_first_lambda =
      match expr with
      | ScmConst'(x) -> [] 
      | ScmVar'(x) -> []
      | ScmIf'(test,dit,dif) -> (writes arg test enclosing_lambda is_first_lambda) @ (writes arg dit enclosing_lambda is_first_lambda) @ (writes arg dif enclosing_lambda is_first_lambda)
      | ScmSeq'(list) -> List.fold_left (List.append) [] (List.map (fun x -> writes arg x enclosing_lambda is_first_lambda) list)
      | ScmOr'(list) -> List.fold_left (List.append) [] (List.map (fun x -> writes arg x enclosing_lambda is_first_lambda) list)
      | ScmSet'(VarBound(name, major, minor),value) -> if name = arg then [enclosing_lambda] @ writes arg value enclosing_lambda is_first_lambda else writes arg value enclosing_lambda is_first_lambda
      | ScmSet'(VarParam(name, major),value) -> if name = arg then [enclosing_lambda] @ writes arg value enclosing_lambda is_first_lambda else writes arg value enclosing_lambda is_first_lambda 
      | ScmSet'(var, value) -> writes arg value enclosing_lambda is_first_lambda
      | ScmApplic'(f,args) -> (writes arg f enclosing_lambda is_first_lambda) @ ( List.fold_left (List.append) [] (List.map (fun x -> writes arg x enclosing_lambda is_first_lambda) args))
      | ScmApplicTP'(f , args) -> (writes arg f enclosing_lambda is_first_lambda) @ ( List.fold_left (List.append) [] (List.map (fun x -> writes arg x enclosing_lambda is_first_lambda) args))
      | ScmLambdaSimple'(args, body) -> if List.mem arg args then [] else if is_first_lambda then writes arg body expr false else writes arg body enclosing_lambda is_first_lambda
      | ScmLambdaOpt'(args, rest_args, body) ->  let united_args = args @ [rest_args] in if List.mem arg united_args then [] else if is_first_lambda then writes arg body expr false else writes arg body enclosing_lambda is_first_lambda
      | _ -> []
      in
      let write_list = writes arg body expr true in
      let rec reads arg expr enclosing_lambda is_first_lambda =
      match expr with
      | ScmConst'(x) -> [] 
      (* change if var bound or param with that name*)
      | ScmVar'(VarBound(name, major, minor)) -> if name = arg then [enclosing_lambda] else []
      | ScmVar'(VarParam(name, major)) -> if name = arg then [enclosing_lambda] else []
      | ScmIf'(test,dit,dif) -> (reads arg test enclosing_lambda is_first_lambda) @ (reads arg dit enclosing_lambda is_first_lambda) @ (reads arg dif enclosing_lambda is_first_lambda)
      | ScmSeq'(list) -> List.fold_left (List.append) [] (List.map (fun x -> reads arg x enclosing_lambda is_first_lambda) list)
      | ScmOr'(list) -> List.fold_left (List.append) [] (List.map (fun x -> reads arg x enclosing_lambda is_first_lambda) list)
      | ScmSet'(var,value) -> (reads arg value enclosing_lambda is_first_lambda)
      | ScmApplic'(f,args) -> (reads arg f enclosing_lambda is_first_lambda) @ ( List.fold_left (List.append) [] (List.map (fun x -> reads arg x enclosing_lambda is_first_lambda) args))
      | ScmApplicTP'(f , args) -> (reads arg f enclosing_lambda is_first_lambda) @ ( List.fold_left (List.append) [] (List.map (fun x -> reads arg x enclosing_lambda is_first_lambda) args))
      | ScmLambdaSimple'(args, body) -> if List.mem arg args then [] else if is_first_lambda then reads arg body expr false else reads arg body enclosing_lambda is_first_lambda
      | ScmLambdaOpt'(args, rest_args, body) -> let united_args = args @ [rest_args] in if List.mem arg united_args then [] else if is_first_lambda then reads arg body expr false else reads arg body enclosing_lambda is_first_lambda
      | _ -> []
      in
      
      let read_list = reads arg body expr true in
      check_share_rib read_list write_list



  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
      match pe with
      | ScmConst'(x) -> pe
      | ScmVar'(x) -> pe
      | ScmIf'(test,dit,dif) -> ScmIf'(test, (run dit in_tail),(run dif in_tail))
      | ScmSeq'(list) -> ScmSeq'(List.map (fun x -> run x false) (without_last_elemnt list) @ [run (last_element list) in_tail])
      | ScmOr'(list) -> ScmOr'(List.map (fun x -> run x false) (without_last_elemnt list) @ [run (last_element list) in_tail])
      (*check if define is tail position *)
      | ScmDef'(var,value) -> ScmDef'(var, run value false)
      | ScmSet'(var,value) -> ScmSet'(var, run value false)
      | ScmLambdaSimple'(args, body) -> ScmLambdaSimple'(args, run body true)
      | ScmLambdaOpt'(args, rest_args, body) -> ScmLambdaOpt'(args, rest_args, run body true)
      | ScmApplic'(f,args) -> if in_tail
          then ScmApplicTP'((run f false), List.map (fun x -> run x false) args)
          else ScmApplic'((run f false), List.map (fun x -> run x false) args)
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;

  let find_reads name enclosing_lambda expr = raise X_not_yet_implemented 

  let rec box_set expr =
    match expr with
      | ScmConst'(x) -> expr
      | ScmVar'(x) -> expr
      | ScmIf'(test,dit,dif) -> ScmIf'(box_set test,box_set dit ,box_set dif)
      | ScmSeq'(list) -> ScmSeq'(List.map (fun x -> box_set x) list)
      | ScmOr'(list) -> ScmOr'(List.map (fun x -> box_set x) list)
      | ScmDef'(var,value) -> ScmDef'(var, box_set value)
      | ScmSet'(var,value) -> ScmSet'(var, box_set value)
      | ScmApplic'(f,args) -> ScmApplic'(box_set f, List.map (fun x -> box_set x) args)
      | ScmApplicTP'(f , args) -> ScmApplicTP'(box_set f, List.map (fun x -> box_set x) args)
      | ScmLambdaSimple'(args, body) -> 
         let vars_should_box = List.filter (fun arg -> this_var_should_box arg expr body) args in let vars_should_box = List.rev vars_should_box in
         ScmLambdaSimple'(args, box_set (new_body body vars_should_box args))
      | ScmLambdaOpt'(args, rest_args, body) -> let new_args = args@[rest_args] in let vars_should_box = List.filter (fun arg -> this_var_should_box arg expr body) new_args in let vars_should_box = List.rev vars_should_box in  ScmLambdaOpt'(args, rest_args, box_set (new_body body vars_should_box new_args))
      | _ -> expr

  let run_semantics expr =
    box_set(
      annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)