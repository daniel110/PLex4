(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))

(*
  ADD FUNCTIONS BELOW
*)

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
                                | _    -> trm (* [x->s]y = y *)
                               )
    | Application(t1, t2)   -> Application((substitute x s t1), (substitute x s t2))
    | Abstraction(y, t)     -> let cmpResult = compare x y in 
                               (match cmpResult with
                                | 0    -> Abstraction(x, t) (* [x->s](\x. t) = \x. t *)
                                | _    -> let isYFreeInS = StringSet.mem y (fv s) in
                                          (match isYFreeInS with 
                                          | false -> Abstraction(y, (substitute x s t))
                                          | true  -> let z = fresh_var (StringSet.add x (StringSet.union (fv s) (fv t))) in
                                                     Abstraction(z, (substitute x s (substitute y (Variable(z)) t)))
                                          )
                               )
  
  
let rec reduce_strict trm = 
    match trm with
    | Application(t1, t2) -> (match t1 with
                             | Abstraction(x, t1Body) -> (* t1 is a value *)
                                                         (match t2 with
                                                          | Abstraction(y, t2Body) -> Some(substitute x t2 t1Body) (* E-AppAbs *)
                                                          | _                      -> (match (reduce_strict t2) with
                                                                                       | Some t2' -> Some(Application(t1, t2')) (* E-APPL2 *)
                                                                                       | None     -> None 
                                                                                      )
                                                         )
                             | _                      -> (* t1 is NOT a value *)  
                                                         (match (reduce_strict t1) with
                                                          | Some t1' -> Some(Application(t1', t2)) (* E-APPL1 *)
                                                          | None     -> None
                                                         )
                            )
    | _                  -> None (* Only applications can be reduced in strict semantic *)
    

let rec reduce_lazy trm = match trm with
| Application(t1,t2) -> (match t1 with
							| Application(t3,t4) -> (match (reduce_lazy t1) with
														| Some t1' -> Some(Application(t1', t2))  (* E-APPL1 *)
														| None -> None 
														)
							| Abstraction(x,trm1)  -> Some(substitute x t2 trm1)  (* E-AppAbs *)
							| _ -> None
							)
| _ -> None  (* Only applications can be reduced in lazy semantic *)


let rec reduce_normal trm = match trm with
| Application(t1,t2) -> let leftCalc = (match t1 with
										| Abstraction(x,trm1)  -> Some(substitute x t2 trm1)  (* E-AppAbs *)
										| Application(t3,t4) -> (match(reduce_normal t1) with
																	| Some t1' -> Some(Application(t1', t2))  (* E-APPL1 *)
																	| None -> None 
																	)							
										| _ -> None
										)
							in (match leftCalc with
								| Some t1' -> Some t1' (* E-APPL1 succeded*)
								| None -> (match (reduce_normal t2) with 
											| Some t2' -> Some(Application(t1, t2')) (* E-APPL2 *)
											| None -> None
											)
						    	      )
| Abstraction(x,trm1) -> (match (reduce_normal trm1) with
								| Some trm1' -> Some(Abstraction(x,trm1')) (* E-ABS *)
								| None -> None
						    	      )
| _ -> None  (* Only applications and abstractions can be reduced in lazy semantic *)







