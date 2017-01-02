(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser


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
  
(* [x->s]trm *)
let rec substitute x s trm =
    match trm with
    | Variable y            -> let cmpResult = compare x y in 
                               (match cmpResult with
                                | 0    -> s   (* [x->s]x = s *)
                                | _    -> y   (* [x->s]y = y *)
                               )
    | Application(t1, t2)   -> Application((substitute x s t1), (substitute x s t2))
    | Abstraction(y, t)     -> let cmpResult = compare x y in 
                               (match cmpResult with
                                | 0    -> Abstraction(x, t) (* [x->s](\x. t) = \x. t *)
                                | _    -> let isYFreeInS = StringSet.mem y (fv s) in
                                          (match isYFreeInS with 
                                          | false -> Abstraction(y, (substitute x s t))
                                          | true  -> let z = fresh_var (StringSet.add x (StringSet.union (fv s) (fv t))) in
                                                     Abstraction(z, (substitute x s (substitute y z t)))
                                          )
                               )
  
(*
  ADD FUNCTIONS BELOW
*)





