(*
  Tests for the lambda calculus parser and reducers.

  EXTEND THIS FILE TO TEST YOUR SOLUTION THOROUGHLY!
*)

open Utils
open Parser
open Reducer

let rec evaluate ~verbose reduce t =
  if verbose then print_string (format_term t) else ();
  match reduce t with
  | None ->
    if verbose then print_string " =/=>\n\n" else ();
    t
  | Some t' ->
    if verbose then print_string " ==>\n\n" else ();
    evaluate ~verbose reduce t'


let test_and_1 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and tru) tru)
"

let test_and_2 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and fls) ((and tru) tru))
"


let env = "
let tru = (\\t. (\\f. t)) in
let fls = (\\t. (\\f. f)) in
let test = (\\l. (\\m. (\\n. ((l m) n)))) in
let and = (\\b. (\\c.  ((b c) fls))) in

let pair = (\\f. (\\s. (\\b.  ((b f) s)))) in
let fst = (\\p. (p tru)) in
let snd = (\\p. (p fls)) in

let c0 = (\\s. (\\z. z)) in
let c1 = (\\s. (\\z. (s z))) in
let c2 = (\\s. (\\z. (s (s z)))) in
let c3 = (\\s. (\\z. (s (s (s z))))) in
let c4 = (\\s. (\\z. (s (s (s (s z)))))) in
let c5 = (\\s. (\\z. (s (s (s (s (s z))))))) in
let c6 = (\\s. (\\z. (s (s (s (s (s (s z)))))))) in
let c7 = (\\s. (\\z. (s (s (s (s (s (s (s z))))))))) in
let c8 = (\\s. (\\z. (s (s (s (s (s (s (s (s z)))))))))) in
let c9 = (\\s. (\\z. (s (s (s (s (s (s (s (s (s z))))))))))) in
let c10 = (\\s. (\\z. (s (s (s (s (s (s (s (s (s (s z)))))))))))) in
let c24 = (\\s. (\\z. (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))))))))))))) in

let scc = (\\n. (\\s. (\\z. (s ((n s) z))))) in
let plus = (\\m. (\\n. (\\s. (\\z. ((m s) ((n s) z)))))) in
let times = (\\m. (\\n. (\\s. (m (n s))))) in
let power = (\\m. (\\n. (n m))) in
let iszero = (\\m. ((m (\\x. fls)) tru)) in
let prd = (let zz = ((pair c0) c0) in
           let ss = (\\p. ((pair (snd p)) ((plus c1) (snd p)))) in
           (\\m. (fst ((m ss) zz)))) in
let leq = (\\m. (\\n. (iszero ((n prd) m)))) in
let equal = (\\m. (\\n. ((and ((leq m) n)) ((leq n) m)))) in

let Y = (\\f. ((\\x. (f (x x))) (\\x. (f (x x))))) in
let Z = (\\f. ((\\x. (f (\\y. ((x x) y)))) (\\x. (f (\\y. ((x x) y)))))) in
"

let test_fact_l = env ^ "
let fact_l = (Y (\\f. (\\n. (((test (iszero n)) c1) (((times n) (f (prd n)))))))) in
((equal (fact_l c2)) c2)
"

let test_fact_s = env ^ "
let fact_s = (Z (\\f. (\\n. ((((test (iszero n)) (\\x. c1)) (\\x. (((times n) (f (prd n)))))) (\\x.x))))) in
((equal (fact_s c2)) c2)
"

let test_fact_l_complex = env ^ "
let fact_l = (Y (\\f. (\\n. (((test (iszero n)) c1) (((times n) (f (prd n)))))))) in
((equal (fact_l c3)) c6)
"

(* very long test  - takes 10 minutes *)
let test_fact_l_complex_long_run = env ^ "
let fact_l = (Y (\\f. (\\n. (((test (iszero n)) c1) (((times n) (f (prd n)))))))) in
((equal (fact_l c4)) c24)
"

let test ~verbose ~sem ~reduce s =
  printf "\nEvaluating:\n%s\nin %s semantics:\n\n" s sem;
  let result = (evaluate ~verbose reduce (parse s)) in
  printf "Result is: %s\n\n" (format_term result)

let test_lazy = test ~sem:"lazy" ~reduce:reduce_lazy
let test_strict = test ~sem:"strict" ~reduce:reduce_strict
let test_normal = test ~sem:"normal-order" ~reduce:reduce_normal
let test_all ~verbose s =
  test_lazy ~verbose s;
  test_strict ~verbose s;
  test_normal ~verbose s


(* ---------- New test Utils ----------- *)

(* Created test runner which get also expected string result *)
let test_Expected ~verbose ~sem ~reduce s expectedStr = 
  printf "\nEvaluating:\n%s\nin %s semantics:\n\n" s sem;
  let result = (evaluate ~verbose reduce (parse s)) in
  let stringRes = format_term result in
	let cmpRes = compare stringRes expectedStr in
		(match cmpRes with
		| 0 -> printf "Success"
		| _ -> printf "Expected: %s ,Got: %s\n" expectedStr stringRes;)


(* added tests deafults to test_Expected *)
let test_lazy_Expected = test_Expected ~sem:"lazy" ~reduce:reduce_lazy
let test_strict_Expected = test_Expected ~sem:"strict" ~reduce:reduce_strict
let test_normal_Expected = test_Expected ~sem:"normal-order" ~reduce:reduce_normal


(* ---------- New tests ----------- *)

(* test 1 *)
let test_basic_1_strict_expected = "(y (\\z.z))"
let test_basic_1_lazy_expected =  "(y (\\z.z))"
let test_basic_1_normal_expected =  "(y (\\z.z))"

let test_basic_1 = "
let inner_f = (\\x. (y x)) in 
(inner_f (\\z.z))
"
(* test 2 *)
let test_basic_2_strict_expected = "((\\x.(y x)) z)"
let test_basic_2_lazy_expected = "(y z)"
let test_basic_2_normal_expected = "(y z)"

let test_basic_2 = "
let inner_f = (\\x. (y x)) in 
(inner_f (z))
"

(* test 3 *)
let test_basic_3_strict_expected = "((\\z.(z z)) y)"
let test_basic_3_lazy_expected = "(y y)"
let test_basic_3_normal_expected =  "(y y)"

let test_basic_3 = "
let inner_f = ((\\x. x) (\\z. (z z))) in 
(inner_f (y))
"

(* test 4 *)
let test_basic_4_strict_expected = "((\\y.((\\z.z) y)) (\\y ((\\z.z) y)))"
let test_basic_4_lazy_expected = "(\\y.((\\z.z) y))"
let test_basic_4_normal_expected = "(\\y.y)"

let test_basic_4 = "
let inner_f = ((\\x. x) (\\z. (z z))) in 
(inner_f (\\y. ((\\z. z) y)))
"

(* test 5 - bad *)
let test_basic_5_strict_expected = "(x (\\y.((\\z.z) y)))"
let test_basic_5_lazy_expected = "(x (\\y.((\\z.z) y)))"
let test_basic_5_normal_expected = "(x (\\y.y))"

let test_basic_5 = "
let inner_f = (x) in 
(inner_f (\\y. ((\\z. z) y)))
"

let () =
  test_all ~verbose:true test_and_1;
  test_all ~verbose:true test_and_2;

  test_lazy ~verbose:false test_fact_l;
  test_lazy ~verbose:false test_fact_l_complex;
  test_strict ~verbose:false test_fact_s;
  test_normal ~verbose:false test_fact_l;
  test_normal ~verbose:false test_fact_s;

  (* new tests*)
	(* test 1*)
	test_lazy_Expected ~verbose:false test_basic_1 test_basic_1_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_1 test_basic_1_strict_expected;
	test_normal_Expected ~verbose:false test_basic_1 test_basic_1_normal_expected;
	(* test 2*)
	test_lazy_Expected ~verbose:false test_basic_2 test_basic_2_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_2 test_basic_2_strict_expected;
	test_normal_Expected ~verbose:false test_basic_2 test_basic_2_normal_expected;
	(* test 3*)
	test_lazy_Expected ~verbose:false test_basic_3 test_basic_3_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_3 test_basic_3_strict_expected;
	test_normal_Expected ~verbose:false test_basic_3 test_basic_3_normal_expected;
	(* test 4*)
	test_lazy_Expected ~verbose:false test_basic_4 test_basic_4_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_4 test_basic_4_strict_expected;
	test_normal_Expected ~verbose:false test_basic_4 test_basic_4_normal_expected;
	(* test 5*)
	test_lazy_Expected ~verbose:false test_basic_5 test_basic_5_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_5 test_basic_5_strict_expected;
	test_normal_Expected ~verbose:false test_basic_5 test_basic_5_normal_expected;
