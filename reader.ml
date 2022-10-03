(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;
 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;

  let abs_gcd a b =
    let x = gcd a b in
    if x > 0 then x
    else -x 
 
  let rec power_shaked a b =
    if b = 0 then 1.0
    else a*. (power_shaked a (b-1)) 

  let power_amit a b =
    if b < 0 then (1.0 /. (power_shaked a (-b)))
    else (power_shaked a b)


 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let foo a b =
  let x = ScmPair (a,b) in
  x

 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
 and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = nt_char_simple in
  let nt2 = star nt2 in
  let nt2 = pack nt2 (fun _ -> ScmVoid) in
  let nt2 = caten nt1 nt2 in
  let nt2 = pack nt2 (fun _ -> ScmVoid) in
  let nt2 = caten nt2 nt_end_of_line_or_file in
  let nt2 = pack nt2(fun _ -> ScmVoid) in
  let nt2 = unitify nt2 in
  nt2 str

 and nt_paired_comment str =  
  let nt_open = char '{' in
  let nt_close = char '}' in
  let nt_without = diff nt_any (disj nt_open nt_close) in
  let nt_b = disj_list [unitify nt_string; unitify nt_followed_char; unitify nt_without] in
  let nt_b_star = star nt_b in
  let nt1 = caten_list [unitify nt_open; unitify nt_b_star; unitify (star nt_paired_comment); unitify nt_b_star; unitify nt_close] in
  let nt1 = unitify nt1 in
  nt1 str

 and nt_sexpr_comment str =  
  let siman = word "#;" in
  let nt1 = star nt_sexpr_comment in
  let nt2 = caten siman nt1 in
  let nt2 = caten nt2 nt_sexpr in
  let nt2 = pack nt2 (fun _ -> ()) in
  nt2 str


 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str

 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str

 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1

 and nt_int str = 
  let nt1 = char '+' in
  let nt1 = caten nt1 nt_integer_part in
  let nt1 = pack nt1 (fun (a,b) -> b) in
  let nt2 = char '-' in
  let nt2 = caten nt2 nt_integer_part in
  let nt2 = pack nt2 (fun (a,b) -> b * (-1)) in
  let nt1 = disj nt1 nt2 in
  let nt1 = disj nt1 nt_integer_part in
  nt1 str

 and nt_frac str = 
  let nt1 = char '/' in
  let nt1 = caten nt_int nt1 in
  let nt1 = pack nt1 (fun (a,b) -> a) in
  let nt1 = caten nt1 nt_integer_part in
  let nt1 = pack nt1 (fun (a,b) ->  if b=0 then raise X_no_match else let x = (abs_gcd a b) in ScmRational (a/x,b/x)) in
  nt1 str

 and nt_integer_part str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun a ->  int_of_string (list_to_string a)) in
  nt1 str

 and nt_mantissa str = 
  let nt1 = pack nt_integer_part (fun a ->
    let str_num = string_of_int a in
    let num_len = String.length str_num in
    let div = power_amit 10.0 num_len in
    let numb = float a in
    let ans = numb /. div in ans) in 
    nt1 str

 and nt_exp_token str =
  let nt1 = char_ci 'e' in
  let nt1 = pack nt1 (fun _ -> 10) in
  let nt2 = word "*10^" in
  let nt2 = pack nt2 (fun _ -> 10) in
  let nt3 = word "*10**" in
  let nt3 = pack nt3 (fun _ -> 10) in
  let nt1 = disj nt1 nt2 in
  let nt1 = disj nt1 nt3 in
  let nt1 = pack nt1 (fun _ -> 10) in
  nt1 str

 and nt_exponent str = 
  let nt1 = caten nt_exp_token nt_int in
  let nt1 = pack nt1 (fun (a,b) -> let a = float a in let x = (power_amit a b) in x)in
  nt1 str

  and nt_float_a str =
    let nt1 = char '.' in
    let int_part = caten nt_integer_part nt1 in
    let int_part = pack int_part (fun (a,b) -> float a) in
    let mantis = caten int_part nt_mantissa in
    let mantis = pack mantis (fun (a,b) -> a+.b) in
    let mantis_exp = caten mantis nt_exponent in
    let mantis_exp = pack mantis_exp (fun (a,b) -> a*.b) in
    let exp = caten int_part nt_exponent in
    let exp = pack exp (fun (a,b) -> a*.b) in
    let nt2 = disj mantis_exp mantis in
    let nt2 = disj nt2 exp in
    let nt2 = disj nt2 int_part in
    nt2 str
  
  and nt_float_b str = 
    let nt1 = char '.' in
    let nt2 = caten nt1 nt_mantissa in
    let nt2 = pack nt2 (fun (a,b) -> b) in
    let nt3 = caten nt2 nt_exponent in
    let nt3 = pack nt3 (fun (a,b) -> a*.b) in
    let nt4 = disj nt3 nt2 in
    nt4 str
  
  and nt_float_c str = 
    let nt1 = caten nt_integer_part nt_exponent in
    let nt1 = pack nt1 (fun (a,b) -> let a = float a in a*.b) in
    nt1 str
  
 and nt_float str = 
  let nt1 = disj nt_float_a nt_float_b in
  let nt1 = disj nt1 nt_float_c in
  let nt2 = char '+' in
  let nt2 = caten nt2 nt1 in
  let nt2 = pack nt2 (fun (a,b) -> b) in
  let nt3 = char '-' in
  let nt3 = caten nt3 nt1 in
  let nt3 = pack nt3 (fun (a,b) -> -1.0*.b) in
  let nt1 = disj nt1 nt2 in
  let nt1 = disj nt1 nt3 in
  let nt1 = pack nt1 (fun a -> ScmReal a) in
  nt1 str

 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str

 and nt_boolean str = 
  let nt1 = word_ci "#t" in
  let nt1 = pack nt1 (fun _ -> true) in
  let nt2 = word_ci "#f" in
  let nt2 = pack nt2 (fun _ -> false) in
  let nt2 = disj nt1 nt2 in
  let nt2 = pack nt2 (fun x -> ScmBoolean x) in
  nt2 str

 and nt_char_simple str = 
  let nt1 = (range ' ' '~') in
  let nt1 = pack nt1 (fun x -> ScmChar x) in
  nt1 str

 and make_named_char char_name ch = 
    let nt1 = word char_name in
    let nt1 = pack nt1 (fun _ -> ScmChar ch) in
    nt1

 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "nul" (char_of_int 0));
                (make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str

 and nt_char_hex str = 
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 (fun a -> let a = int_of_char a in a - 48) in
  let nt2 = range 'a' 'f' in
  let nt2 = pack nt2 (fun a -> let a = int_of_char a in a - 87) in
  let nt3 = range 'A' 'F' in
  let nt3 = pack nt3 (fun a -> let a = int_of_char a in  a -55) in
  let nt2 = disj nt2 nt3 in
  let nt1 = disj nt1 nt2 in
  nt1 str

 and nt_help_hex str =
  let nt1 = char_ci 'x' in
  let nt2 = caten nt_char_hex nt_char_hex in
  let nt2 = caten nt1 nt2 in
  let nt2 = pack nt2 (fun (a,b) -> b) in
  let nt2 = pack nt2 (fun (a,b) -> a*16 + b) in
  let nt2 = pack nt2 (fun a -> char_of_int a) in
  let nt2 = pack nt2 (fun a -> ScmChar a) in
  nt2 str

 and nt_followed_char str =
  let nt2 = word "#\\" in
  let nt3 = disj_list [nt_help_hex; nt_char_named; nt_char_simple] in
  let nt3 = caten nt2 nt3 in
  let nt3 = pack nt3 (fun (a,b) -> b) in
  nt3 str

 and nt_char str = 
  let nt2 = word "#\\" in
  let nt3 = disj_list [nt_help_hex; nt_char_named; nt_char_simple] in
  let nt3 = caten nt2 nt3 in
  let nt3 = pack nt3 (fun (a,b) -> b) in
  (* let nt3 = not_followed_by nt3 nt_any in *)
  nt3 str

 and nt_symbol_char str = 
    let numbers = range '0' '9' in
    let letters = range_ci 'a' 'z' in
    let sign1 = char '!' in
    let sign2 = char '$' in
    let sign3 = char '^' in
    let sign4 = char '*' in
    let sign5 = char '-' in
    let sign6 = char '_' in
    let sign7 = char '=' in
    let sign8 = char '+' in
    let sign9 = char '<' in
    let sign10 = char '>' in
    let sign11 = char '?' in
    let sign12 = char '/' in
    let sign13 = char ':' in
    let allLetters = disj numbers letters in
    let allLetters = disj allLetters sign1 in
    let allLetters = disj allLetters sign2 in
    let allLetters = disj allLetters sign3 in
    let allLetters = disj allLetters sign4 in
    let allLetters = disj allLetters sign5 in
    let allLetters = disj allLetters sign6 in
    let allLetters = disj allLetters sign7 in
    let allLetters = disj allLetters sign8 in
    let allLetters = disj allLetters sign9 in
    let allLetters = disj allLetters sign10 in
    let allLetters = disj allLetters sign11 in
    let allLetters = disj allLetters sign12 in
    let allLetters = disj allLetters sign13 in
    allLetters str

 and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  nt1 str

 and nt_strin_char str = 
    let nt_str_char = disj nt_stringLiteralChar nt_stringHexchar in
    let nt_str_char = disj nt_str_char nt_stringMetaChar in
    nt_str_char str

 and nt_string str = 
  let start = ScmSymbol "string-append" in
  let nt_open = word "\"" in
  let a_star = star nt_strin_char in 
  let a_star = pack a_star(fun a -> list_to_string a) in
  let a_star = pack a_star(fun a -> ScmString a) in
  let a_plus = plus nt_strin_char in 
  let a_plus = pack a_plus(fun a -> list_to_string a) in
  let a_plus = pack a_plus(fun a -> ScmString a) in
  let nt_chars_inter = caten a_plus nt_stringInterpolated in
  let nt_chars_inter = pack nt_chars_inter(fun (a,b) -> [a;b]) in
  let nt_inter_chars = caten nt_stringInterpolated a_plus in
  let nt_inter_chars = pack nt_inter_chars(fun (a,b) -> [a;b]) in
  let nt_chars_inter_chars = caten a_plus nt_stringInterpolated in
  let nt_chars_inter_chars = pack nt_chars_inter_chars(fun (a,b) -> [a;b]) in
  let nt_chars_inter_chars = caten nt_chars_inter_chars a_plus in
  let nt_chars_inter_chars = pack nt_chars_inter_chars(fun (a,b) -> a@(b::[])) in
  (* let nt_two_inter = caten a_star nt_stringInterpolated in
  let nt_two_inter = pack nt_two_inter(fun (a,b) -> [a;b]) in
  let nt_two_inter = caten nt_two_inter nt_two_inter in
  let nt_two_inter = pack nt_two_inter(fun (a,b) -> a@b) in
  let nt_two_inter = caten nt_two_inter a_star in
  let nt_two_inter = pack nt_two_inter(fun (a,b) -> a@(b::[])) in *)
  let nt_adj_inters = caten nt_stringInterpolated nt_stringInterpolated in
  let nt_adj_inters = pack nt_adj_inters(fun (a,b) -> [a;b]) in 
  (* let nt_inter_pl_inter = caten nt_stringInterpolated a_plus in
  let nt_inter_pl_inter = pack nt_inter_pl_inter( fun (a,b) -> [a;b]) in
  let nt_inter_pl_inter = caten nt_inter_pl_inter nt_stringInterpolated in
  let nt_inter_pl_inter = pack nt_inter_pl_inter(fun (a,b) -> a@(b::[])) in *)
  let nt_chars_inter_inter = caten a_plus nt_stringInterpolated in
  let nt_chars_inter_inter = pack nt_chars_inter_inter(fun (a,b) -> [a;b]) in
  let nt_chars_inter_inter = caten nt_chars_inter_inter nt_stringInterpolated in
  let nt_chars_inter_inter = pack nt_chars_inter_inter(fun (a,b) -> a@(b::[])) in
  let nt_inter_inter_chars = caten nt_stringInterpolated nt_stringInterpolated in
  let nt_inter_inter_chars = pack nt_inter_inter_chars(fun (a,b) -> [a;b]) in 
  let nt_inter_inter_chars = caten nt_inter_inter_chars a_plus in
  let nt_inter_inter_chars = pack nt_inter_inter_chars(fun (a,b) -> a@(b::[])) in
  let nt_chars_inter_chars_inter = caten nt_chars_inter_chars nt_stringInterpolated in
  let nt_chars_inter_chars_inter = pack nt_chars_inter_chars_inter(fun (a,b) -> a@(b::[])) in
  let nt_inter_chars_inter_chars = caten nt_stringInterpolated a_plus in
  let nt_inter_chars_inter_chars = pack nt_inter_chars_inter_chars( fun (a,b) -> [a;b]) in
  let nt_inter_chars_inter_chars = caten nt_inter_chars_inter_chars nt_stringInterpolated in
  let nt_inter_chars_inter_chars = pack nt_inter_chars_inter_chars(fun (a,b) -> a@(b::[])) in
  let nt_inter_chars_inter_chars = caten nt_inter_chars_inter_chars a_plus in
  let nt_inter_chars_inter_chars = pack nt_inter_chars_inter_chars(fun (a,b) -> a@(b::[])) in
  let nt_chars_inter_inter_chars = caten nt_chars_inter_inter a_plus in
  let nt_chars_inter_inter_chars = pack nt_chars_inter_inter_chars(fun (a,b) -> a@(b::[])) in
  let nt_chars_inter_chars_inter_chars = caten nt_chars_inter_chars_inter a_plus in
  let nt_chars_inter_chars_inter_chars = pack nt_chars_inter_chars_inter_chars(fun (a,b) -> a@(b::[])) in
  let nt_inter_chars_inter = caten nt_inter_chars nt_stringInterpolated in
  let nt_inter_chars_inter = pack nt_inter_chars_inter(fun (a,b) -> a@(b::[])) in
  let nt1 = disj_list [nt_chars_inter_chars_inter_chars; nt_chars_inter_chars_inter; nt_chars_inter_inter_chars; nt_chars_inter_inter; nt_chars_inter_chars; nt_chars_inter;
   nt_inter_chars_inter_chars; nt_inter_chars_inter; nt_inter_chars; nt_inter_inter_chars; nt_adj_inters] in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun a -> List.fold_right List.append a []) in
  let nt1 = pack nt1 (fun a -> ScmPair(start, List.fold_right foo a ScmNil )) in
  let nt_final = disj_list [nt1; nt_stringInterpolated; a_star] in
  let nt_final = caten nt_open nt_final in
  let nt_final = pack nt_final (fun (a,b) -> b) in
  let nt_final = caten nt_final nt_open in
  let nt_final = pack nt_final (fun (a,b) -> a) in
  nt_final str



 and nt_stringChar str = 
    let nt1 = disj nt_stringHexchar nt_stringLiteralChar in
    let nt2 = disj nt1 nt_stringMetaChar in
    nt2 str

 and nt_stringHexchar str = 
    let nt1 = word_ci "\\x" in 
    let nt2 = caten nt_char_hex nt_char_hex in
    let nt2 = pack nt2 (fun (a,b) -> a*16 +b) in
    let nt2 = caten nt1 nt2 in
    let nt2 = pack nt2 (fun (a,b) -> char_of_int b) in
    let nt3 = char ';' in
    let nt3 = caten nt2 nt3 in
    let nt3 = pack nt3 (fun (a,b) -> a) in
    nt3 str

  and nt_stringLiteralChar str =
    let a = char_of_int 0 in
    let nt1 = range a '!' in
    let nt2 = range '#' '[' in
    let nt3 = range ']' '}' in
    let nt1 = disj nt1 nt2 in
    let nt1 = disj nt1 nt3 in
    nt1 str

  and nt_stringMetaChar str = 
    let nt1 = word "\\t" in
    let nt1 = pack nt1 (fun a -> char_of_int(9)) in
    let nt2 = word "\\f" in
    let nt2 = pack nt2 (fun a -> char_of_int(12)) in
    let nt3 = word "\\n" in
    let nt3 = pack nt3 (fun a -> char_of_int(10)) in
    let nt4 = word "\\r" in
    let nt4 = pack nt4 (fun a -> char_of_int(13)) in
    let nt5 = word "~~" in
    let nt5 = pack nt5 (fun _ -> char_of_int(126)) in
    let nt6 = word "\\\\" in
    let nt6 = pack nt6 (fun _ -> char_of_int(92)) in
    let nt7 = word "\\\"" in
    let nt7 = pack nt7 (fun _ -> char_of_int(34)) in 
    let nt7 = disj nt7 nt6 in
    let nt7 = disj nt7 nt5 in
    let nt7 = disj nt7 nt4 in
    let nt7 = disj nt7 nt3 in
    let nt7 = disj nt7 nt2 in
    let nt7 = disj nt7 nt1 in
    nt7 str

  and nt_stringInterpolated str = 
    let form = ScmSymbol "format" in
    let tilda = ScmString "~a" in
    let nt1 = word "~{" in
    let nt_close = char '}' in
    let nt_spaces = char ' ' in
    let nt_spaces = star nt_spaces in
    let nt3 = caten nt1 nt_spaces in
    let nt3 = pack nt3 (fun (a,b) -> ()) in
    let nt4 = caten nt3 nt_sexpr in
    let nt4 = pack nt4 (fun (a,b) -> b) in
    let nt5 = caten nt4 nt_spaces in
    let nt5 = pack nt5 (fun (a,b) -> a) in
    let nt6 = caten nt5 nt_close in
    let nt6 = pack nt6 (fun (a,b) -> ScmPair (form, ScmPair (tilda ,ScmPair (a ,ScmNil)))) in
    nt6 str

 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str

 and nt_pr_list str =
    let init = ScmNil in
    let nt_spaces = char ' ' in
    let nt_spaces = star nt_spaces in
    let nt_open = char '(' in
    let nt_open = caten nt_open nt_spaces in
    let nt_open = unitify nt_open in
    let nt_close = char ')' in
    let nt_close = caten nt_spaces nt_close in
    let nt_close = unitify nt_close in
    let nt_inside = star nt_sexpr in
    let nt_inside = pack nt_inside (fun a -> List.fold_right foo a init) in
    let nt1 = caten nt_open nt_inside in
    let nt1 = pack nt1 (fun (a,b) -> b) in
    let nt1 = caten nt1 nt_close in
    let nt1 = pack nt1 (fun (a,b) -> a) in
    nt1 str 

  
  and nt_im_list str =  
    let nt1 = char '(' in
    let nt2 = plus nt_sexpr in
    let nt3 = word ". " in
    let nt4 = nt_sexpr in
    let nt5 = char ')' in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (a,b) -> b) in
    let nt1 = caten nt1 nt3 in
    let nt1 = pack nt1 (fun (a,b) -> a) in
    let nt1 = caten nt1 nt4 in
    let nt1 = pack nt1 (fun (a,b) -> List.fold_right foo a b) in
    let nt1 = caten nt1 nt5 in
    let nt1 = pack nt1 (fun (a,b) -> a) in
    nt1 str

 and nt_list str = 
  let nt1 = disj nt_pr_list nt_im_list in
  nt1 str

 and nt_quoted str = 
    let x = ScmSymbol "quote" in
    let nt1 = word "'" in 
    let nt2 = caten nt1 nt_sexpr in
    let nt2 = pack nt2 (fun (a,b) -> ScmPair (x , ScmPair (b ,ScmNil))) in
    nt2 str 
  
  and nt_quasi_quoted str = 
    let x = ScmSymbol "quasiquote" in
    let nt1 = word "`" in 
    let nt2 = caten nt1 nt_sexpr in
    let nt2 = pack nt2 (fun (a,b) -> ScmPair (x , ScmPair (b ,ScmNil))) in
    nt2 str 
  
  and nt_unquoted str = 
    let x = ScmSymbol "unquote" in
    let nt1 = char ',' in 
    let nt2 = caten nt1 nt_sexpr in
    let nt2 = pack nt2 (fun (a,b) -> ScmPair (x , ScmPair (b ,ScmNil))) in
    nt2 str 
  
  and nt_unquote_splicing str = 
    let x = ScmSymbol "unquote-splicing" in
    let nt1 = word ",@" in 
    let nt2 = caten nt1 nt_sexpr in
    let nt2 = pack nt2 (fun (a,b) -> ScmPair (x , ScmPair (b ,ScmNil))) in
    nt2 str 
    
 and nt_quoted_forms str = 
  let nt1 = disj nt_unquote_splicing nt_unquoted in
  let nt1 = disj nt1 nt_quasi_quoted in
  let nt1 = disj nt1 nt_quoted in
  nt1 str
  
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;