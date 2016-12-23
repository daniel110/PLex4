(*

  A toy regular expressions package implemented in OCaml

  Adapted to OCaml from Robert Harper's "Programming in Standard ML":
  http://www.cs.cmu.edu/~rwh/smlbook/book.pdf
  http://www.cs.cmu.edu/~rwh/smlbook/examples/regexp.sml

*)

open Core.Std

type token = AtSign | Percent | Literal of char |
    PlusSign | TimesSign | Asterisk | LParen | RParen

let rec tokenize = function
(* the abobe is shortcut for:
   let rec tokenize x = match x with
*)
  | [] -> []
  | '+' :: cs -> PlusSign :: tokenize cs
  | '.' :: cs -> TimesSign :: tokenize cs
  | '*' :: cs -> Asterisk :: tokenize cs
  | '(' :: cs -> LParen :: tokenize cs
  | ')' :: cs -> RParen :: tokenize cs
  | '@' :: cs -> AtSign :: tokenize cs
  | '%' :: cs -> Percent :: tokenize cs
  | ' ' :: cs -> tokenize cs
  | c :: cs -> Literal c :: tokenize cs


(* a version with proper escape mechanism: *)

exception LexicalError
let rec tokenize = function
  | [] -> []
  | '+' :: cs -> PlusSign :: tokenize cs
  | '.' :: cs -> TimesSign :: tokenize cs
  | '*' :: cs -> Asterisk :: tokenize cs
  | '(' :: cs -> LParen :: tokenize cs
  | ')' :: cs -> RParen :: tokenize cs
  | '@' :: cs -> AtSign :: tokenize cs
  | '%' :: cs -> Percent :: tokenize cs
  | ' ' :: cs -> tokenize cs
  | ['\\'] -> raise LexicalError
  | '\\' :: c :: cs  -> Literal c :: tokenize cs
  | c :: cs -> Literal c :: tokenize cs
(*
  The last two cases can be combined:
  | '\\' :: c :: cs | c :: cs -> Literal c :: tokenize cs
*)


type regexp = Zero | One | Char of char |
    Plus of regexp * regexp | Times of regexp * regexp |
    Star of regexp


exception SyntaxError of string


(*
   Grammar:

   exp ::= term | term + exp
   term ::= factor | factor . term
   factor ::= atom | atom*
   atom ::= @ | % | a | (exp)
*)


let rec parse_exp ts =
  let r, ts' = parse_term ts in
  match ts' with
  | PlusSign :: ts'' -> let (r', ts''') = parse_exp ts'' in
			Plus (r, r'), ts'''
  | _ -> r, ts'


and parse_term ts =
  let r, ts' = parse_factor ts in
  match ts' with
  | TimesSign :: ts'' -> let (r', ts''') = parse_term ts'' in
			 Times (r, r'), ts'''
  | _ -> r, ts'


and parse_factor ts =
  let r, ts' = parse_atom ts in
  match ts' with
  | Asterisk :: ts'' -> (Star r), ts''
  | _ -> r, ts'


and parse_atom = function
  | [] -> raise (SyntaxError "Factor expected\n")
  | AtSign :: ts -> Zero, ts
  | Percent :: ts -> One, ts
  | (Literal c) :: ts -> (Char c), ts
  | LParen :: ts -> let (r, ts') = parse_exp ts in (
		    match ts' with
		    | RParen :: ts'' -> r, ts''
		    | _ -> raise (SyntaxError "Right-parenthesis expected\n")
  )
  | _ -> raise (SyntaxError "Unexpected token\n")


let parse s = let (r, ts) =
		try s |> String.to_list |> tokenize |> parse_exp with
		  LexicalError -> raise (SyntaxError "Illegal input.\n")
	      in
	      match ts with
	      | [] -> r
	      | _ -> raise (SyntaxError "Unexpected input.\n")


let rec format_exp = function
  | Zero -> "@"
  | One -> "%"
  | Char '@' -> "\\@"
  | Char '%' -> "\\%"
  | Char '\\' -> "\\\\"
  | Char c -> Char.to_string c
  | Plus (r1, r2) -> let s1 = format_exp r1 in
		     let s2 = format_exp r2 in
		     "(" ^ s1 ^ "+" ^ s2 ^ ")"
  | Times (r1, r2) -> (format_exp r1) ^ "." ^ (format_exp r2)
  | Star r -> "(" ^ (format_exp r) ^ ")*"


let rec match_exp' r cs k =
  match r with
  | Zero -> false
  | One -> k cs
  | Char c -> (match cs with [] -> false | c' :: cs' -> c=c' && k cs')
  | Plus (r1, r2) -> (match_exp' r1 cs k) || (match_exp' r2 cs k)
  | Times (r1, r2) -> match_exp' r1 cs (fun cs' -> match_exp' r2 cs' k)
  | Star r1 -> k cs || match_exp' r1 cs (fun cs' -> match_exp' r cs' k)


let match_exp r s =
  match_exp' r (String.to_list s) (function [] -> true | _ -> false)


(*
   The previous implementation fails on r* where Language(r) contains the
   empty string. The following one does not:
*)

let rec match_exp_fixed' r cs k =
  match r with
  | Zero -> false
  | One -> k cs
  | Char c -> (match cs with [] -> false | c' :: cs' -> c=c' && k cs')
  | Plus (r1, r2) -> (match_exp_fixed' r1 cs k) || (match_exp_fixed' r2 cs k)
  | Times (r1, r2) -> match_exp_fixed' r1 cs (fun cs' -> match_exp_fixed' r2 cs' k)
  | Star r1 ->
    k cs ||
    let n = List.length cs in
    let k' cs' = (List.length cs') < n && match_exp_fixed' r cs' k in
    match_exp_fixed' r1 cs k'


let match_exp_fixed r s =
  match_exp_fixed' r (String.to_list s) (function [] -> true | _ -> false)