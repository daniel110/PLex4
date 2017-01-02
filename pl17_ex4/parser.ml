(*
  Parser for lambda-calculus.
*)

open Utils
open Lexer


(* AST for lambda expressions - DO NOT MODIFY THIS TYPE *)
type term = | Variable of string
      | Abstraction of string * term
      | Application of term * term

(*
  Concrete Syntax:
  t ::= id | (\id.t) | (t1 t2) | (t) | let id=t1 in t2

  Abstract Syntax:
  term ::= id | \id.term | term1 term2
*)

exception SyntaxError of string

(*
  ADD FUNCTIONS BELOW
*)

let rec parse_term ts = 
  match ts with
  | (Literal id) :: ts'->(Variable id) ,ts'
   
  | LParen :: LambdaTok :: (Literal id) :: DotTok :: ts'-> let (r,ts'')=parse_term ts' in (match ts'' with
                          | RParen::ts'' -> Abstraction (id,r), ts''
                          | _ -> raise (SyntaxError "Invalid syntax: LParen is expected.\n")
                        )
  | LParen :: ts' -> let (r,ts'')=parse_term ts' in (match ts'' with
                  | RParen::ts''' -> r,ts'''
                  | [] -> raise (SyntaxError "Invalid syntax.\n")
                  | _ -> let (r',ts''')=parse_term ts'' in (match ts''' with
                              | RParen::ts'''' -> Application(r,r'),ts''''
                              | _ -> raise (SyntaxError "Invalid syntax: RParen is expected.\n")
                              )
              )
  | LetTok :: (Literal id) :: EqTok :: ts' -> let (r,ts'')=parse_term ts' in (match ts'' with
                    | InTok :: ts''' -> let (r',ts'''') = parse_term ts''' in (match ts'''' with  
                                    | _ -> Application(Abstraction(id,r'),r),ts''''
                                    )
                    | _ -> raise (SyntaxError "Invalid syntax: InTok is expected.\n")
                    )
  | _ -> raise (SyntaxError "Invalid syntax of term\n")


let parse s = let (r, ts) =
     s |> string_to_list |> tokenize |> parse_term in
        match ts with
        | [] -> r
        | _ -> raise (SyntaxError "Unexpected input.\n")

let rec format_term = function
  | Variable str -> str
  | Abstraction (str,t) -> "("^"\\"^str^"."^(format_term t)^")"
  | Application (t1,t2) -> let t1'=format_term t1 in
               let t2'=format_term t2 in
               "("^t1'^" "^t2'^")"
               
               