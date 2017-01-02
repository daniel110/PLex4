(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser2


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))
let possible_variables_set=StringSet.of_list possible_variables


(* I used StringSet operations from here: https://ocaml.org/learn/tutorials/modules.html *)
let rec fv term = 
  match term with
| Variable x -> StringSet.singleton x
| Application(t1,t2) -> StringSet.union (fv t1) (fv t2)
| Abstraction(x,t) -> StringSet.remove x (fv t)

let fresh_var t =
let temp = StringSet.filter (fun str -> if StringSet.mem str t then false else true) possible_variables_set 
in (let temp2=StringSet.is_empty temp in
 match temp2 with 
 | true -> raise OutOfVariablesError
 | false -> StringSet.choose temp
)
  
(* [x->s]t *)
let rec substitute x s t =
    match t with
    | Variable y            -> let cmpResult = compare x y in 
                               (match cmpResult with
                                | 0    -> s (* [x->s]x = s *)
                                | _    -> t (* [x->s]y = y *))
    | Application(t1, t2)   ->  Application((substitute x s t1), (substitute x s t2))
    | _             -> raise (SyntaxError "Not Implemented yet.")
  
(*
  ADD FUNCTIONS BELOW
*)





