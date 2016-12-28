(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser2


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))


(* I used StringSet operations from here: https://ocaml.org/learn/tutorials/modules.html *)
let rec fv term = 
  match term with
| Variable x -> StringSet.singleton x
| Application(t1,t2) -> StringSet.union (fv t1) (fv t2)
| Abstraction(x,t) -> StringSet.remove x (fv t)


(*
  ADD FUNCTIONS BELOW
*)
