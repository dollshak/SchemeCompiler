#use "reader.ml";; 

let char_to_scheme_str c = 
match c with 
| '\000' -> "#\\nul"
| '\n' -> "#\\newline"
| '\r' -> "#\\return"
| '\t' -> "#\\tab"
| '\012' -> "#\\page"
| ' ' -> "#\\space"
| _ -> Printf.sprintf "#\\%c" c;;

let rec sexpr_to_scheme_str sexpr = 
match sexpr with
| Bool(true) -> "#t"
| Bool(false) -> "#f"
| Nil -> "()"
| Number(Float f) -> Printf.sprintf "%f" f
| Number(Int n) -> Printf.sprintf "%d" n
| Char(c) -> char_to_scheme_str c
| String(s) -> Printf.sprintf "\"%s\"" s
| Symbol(s) -> s
| Pair(car, cdr) -> Printf.sprintf "(%s . %s)" 
                        (sexpr_to_scheme_str car) 
                        (sexpr_to_scheme_str cdr);;

let input_file = Sys.argv.(1);;

let read_test_file file = 
let channel = open_in file in
really_input_string channel (in_channel_length channel);;

let input = 
String.trim (read_test_file input_file);;

let output =
let output_sexprs = Reader.read_sexprs input in
let output_sexprs_str = List.map sexpr_to_scheme_str output_sexprs in
String.concat " " output_sexprs_str;;

let scheme_eq_expr = Printf.sprintf "(equal? '(%s) '(%s))" input output;;
Printf.printf "`(%s: ,%s)" input_file scheme_eq_expr;;
