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
  printf "\nEvaluating:%s\nin %s semantics:\n" s sem;
  let result = (evaluate ~verbose reduce (parse s)) in
  let stringRes = format_term result in
	let cmpRes = compare stringRes expectedStr in
		(match cmpRes with
		| 0 -> printf "Success\n";
		| _ -> printf "Expected: %s ,Got: %s\n" expectedStr stringRes;)


(* added tests deafults to test_Expected *)
let test_lazy_Expected = test_Expected ~sem:"lazy" ~reduce:reduce_lazy
let test_strict_Expected = test_Expected ~sem:"strict" ~reduce:reduce_strict
let test_normal_Expected = test_Expected ~sem:"normal-order" ~reduce:reduce_normal


(* parser check report error *)
let test_parser s = 
		try
			format_term (parse s)
		with
		SyntaxError err ->  err

let test_parser_expected s expectedValue  =
	printf "Parsing:\n%s\n" s;
	let strRes = test_parser s in
		(match strRes with
			| ev when ev = expectedValue -> printf "Success\n";
			| _ -> printf "Expected: %s ,Got: %s\n" expectedValue strRes;
		)
        
(* substitute tests *)
let test_substitute x t1 t2 =
		try
			format_term (substitute x (parse t1) (parse t2))
		with
		OutOfVariablesError ->  "OutOfVariablesError"

let test_substitute_expected x t1 t2 expectedValue = 
    printf "Substituting:\n[%s->%s]%s\n" x t1 t2;
    let strRes = test_substitute x t1 t2 in
        (match strRes with
			| ev when ev = expectedValue -> printf "Success\n";
			| _ -> printf "Expected: %s ,Got: %s\n" expectedValue strRes;
		)
		
		

(* ---------- New tests ----------- *)

(* test 1 *)
let test_basic_1_strict_expected = "(y (\\z. z))"
let test_basic_1_lazy_expected =  "(y (\\z. z))"
let test_basic_1_normal_expected =  "(y (\\z. z))"

let test_basic_1 = "
let inner_f = (\\x. (y x)) in 
(inner_f (\\z. z))
"
(* test 2 *)
let test_basic_2_strict_expected = "((\\x. (y x)) z)"
let test_basic_2_lazy_expected = "(y z)"
let test_basic_2_normal_expected = "(y z)"

let test_basic_2 = "
let inner_f = (\\x. (y x)) in 
(inner_f (z))
"

(* test 3 *)
let test_basic_3_strict_expected = "((\\z. (z z)) y)"
let test_basic_3_lazy_expected = "(y y)"
let test_basic_3_normal_expected =  "(y y)"

let test_basic_3 = "
let inner_f = ((\\x. x) (\\z. (z z))) in 
(inner_f (y))
"

(* test 4 *)
let test_basic_4_strict_expected = "(\\y. ((\\z. z) y))"
let test_basic_4_lazy_expected = "(\\y. ((\\z. z) y))"
let test_basic_4_normal_expected = "(\\y. y)"

let test_basic_4 = "
let inner_f = ((\\x. x) (\\z. (z z))) in 
(inner_f (\\y. ((\\z. z) y)))
"

(* test 5  *)
let test_basic_5_strict_expected = "((\\inner_f. (inner_f (\\y. ((\\z. z) y)))) x)"
let test_basic_5_lazy_expected = "(x (\\y. ((\\z. z) y)))"
let test_basic_5_normal_expected = "(x (\\y. y))"

let test_basic_5 = "
let inner_f = (x) in 
(inner_f (\\y. ((\\z. z) y)))
"

(* test 6  *)
let test_basic_6_strict_expected = "(x (\\y. ((\\z. z) y)))"
let test_basic_6_lazy_expected = "(x (\\y. ((\\z. z) y)))"
let test_basic_6_normal_expected = "(x (\\y. y))"

let test_basic_6 = "
(x (\\y. ((\\z. z) y)))
"



let () =
  test_all ~verbose:true test_and_1;
  test_all ~verbose:true test_and_2;

  test_lazy ~verbose:false test_fact_l;
  test_lazy ~verbose:false test_fact_l_complex;
  test_strict ~verbose:false test_fact_s;
  test_normal ~verbose:false test_fact_l;
  test_normal ~verbose:false test_fact_s;

  (* reduce new tests *)
	(* test 1*)
	printf "\nTest 1\n";
	test_lazy_Expected ~verbose:false test_basic_1 test_basic_1_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_1 test_basic_1_strict_expected;
	test_normal_Expected ~verbose:false test_basic_1 test_basic_1_normal_expected;
	(* test 2*)
	printf "\nTest 2\n";
	test_lazy_Expected ~verbose:false test_basic_2 test_basic_2_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_2 test_basic_2_strict_expected;
	test_normal_Expected ~verbose:false test_basic_2 test_basic_2_normal_expected;
	(* test 3*)
	printf "\nTest 3\n";
	test_lazy_Expected ~verbose:false test_basic_3 test_basic_3_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_3 test_basic_3_strict_expected;
	test_normal_Expected ~verbose:false test_basic_3 test_basic_3_normal_expected;
	(* test 4*)
	printf "\nTest 4\n";
	test_lazy_Expected ~verbose:false test_basic_4 test_basic_4_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_4 test_basic_4_strict_expected;
	test_normal_Expected ~verbose:false test_basic_4 test_basic_4_normal_expected;
	(* test 5*)
	printf "\nTest 5\n";
	test_lazy_Expected ~verbose:false test_basic_5 test_basic_5_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_5 test_basic_5_strict_expected;
	test_normal_Expected ~verbose:false test_basic_5 test_basic_5_normal_expected;
	(* test 6*)
	printf "\nTest 6\n";
	test_lazy_Expected ~verbose:false test_basic_6 test_basic_6_lazy_expected;
	test_strict_Expected ~verbose:false test_basic_6 test_basic_6_strict_expected;
	test_normal_Expected ~verbose:false test_basic_6 test_basic_6_normal_expected;


  (* parser tests *)
	printf "\nParsing tests:\n";
	(* test 7*)
	printf "\nTest 7\n";
	test_parser_expected "(x" "Invalid syntax: RParen is expected.\n";

	(* test 8*)
	printf "\nTest 8\n";
	test_parser_expected "(x)" "x";	

	(* test 9*)
	printf "\nTest 9\n";
	test_parser_expected "x" "x";

	(* test 10*)
	printf "\nTest 10\n";
	test_parser_expected "(\\x. (x x))" "(\\x. (x x))";

	(* test 11*)
	printf "\nTest 11\n";
	test_parser_expected "\\x. (x x)" "Invalid syntax of term\n";

	(* test 12*)
	printf "\nTest 12\n";
	test_parser_expected "((\\x. (y x)" "Invalid syntax: RParen is expected.\n";

	(* test 13*)
	printf "\nTest 13\n";
	test_parser_expected "(\\x.(x x)) ((((\\x. (%% x)))" "Unexpected input.\n";

	(* test 14*)
	printf "\nTest 14\n";
	test_parser_expected "((\\x.(x x)) ((((\\x. (%% x))))" "Invalid syntax: RParen is expected.\n";

	(* test 15*)
	printf "\nTest 15\n";
	test_parser_expected "(x x" "Invalid syntax: RParen is expected.\n";

    
    (* substitute tests *)
    printf "\nSubstitute tests:\n";
    (* test 16 *)
    printf "\nTest 16\n";
    test_substitute_expected "x" "y" "x" "y";
    
    (* test 17 *)
    printf "\nTest 17\n";
    test_substitute_expected "x" "x" "x" "x";
    
    (* test 18 *)
    printf "\nTest 18\n";
    test_substitute_expected "x" "(\\y. y)" "x" "(\\y. y)";
    
    (* test 19 *)
    printf "\nTest 19\n";
    test_substitute_expected "x" "(\\x. x)" "x" "(\\x. x)";
    
    (* test 20 *)
    printf "\nTest 20\n";
    test_substitute_expected "x" "(x y)" "x" "(x y)";
    
    (* test 21 *)
    printf "\nTest 21\n";
    test_substitute_expected "y" "z" "y" "z";
    
    (* test 22 *)
    printf "\nTest 22\n";
    test_substitute_expected "x" "s" "y" "y";
    
    (* test 23 *)
    printf "\nTest 23\n";
    test_substitute_expected "x" "x" "y" "y";
    
    (* test 24 *)
    printf "\nTest 24\n";
    test_substitute_expected "x" "(\\x. x)" "y" "y";
    
    (* test 25 *)
    printf "\nTest 25\n";
    test_substitute_expected "x" "s" "(x x)" "(s s)";
        
    (* test 26 *)
    printf "\nTest 26\n";
    test_substitute_expected "x" "s" "(y y)" "(y y)";
         
    (* test 27 *)
    printf "\nTest 27\n";
    test_substitute_expected "x" "s" "((x y) y)" "((s y) y)";
    
    (* test 28 *)
    printf "\nTest 28\n";
    test_substitute_expected "x" "s" "(\\x. t)" "(\\x. t)";
        
    (* test 29 *)
    printf "\nTest 29\n";
    test_substitute_expected "x" "s" "(\\x. (\\x. x))" "(\\x. (\\x. x))";
    
    (* test 30 *)
    printf "\nTest 30\n";
    test_substitute_expected "x" "(t1 t2)" "(\\y. x)" "(\\y. (t1 t2))";
    
    (* test 31 *)
    printf "\nTest 31\n";
    test_substitute_expected "x" "(x y)" "(\\y. (x y))" "(\\A. ((x y) A))";
    
    (* test 32 *)
    printf "\nTest 32\n";
    test_substitute_expected "x" "(u r)" "(x (\\x. x))" "((u r) (\\x. x))";
    
    (* test 33 *)
    printf "\nTest 33\n";
    test_substitute_expected "x" "(\\x. (x x))" "(x x)" "((\\x. (x x)) (\\x. (x x)))";
    
    (* test 34 *)
    printf "\nTest 34\n";
    test_substitute_expected "x" "((\\u. u)(\\w. w))" "(\\y. ((\\z. z) y))" "(\\y. ((\\z. z) y))";
    
    (* test 35 *)
    printf "\nTest 35\n";
    let term_with_all_variables = "(\\A. (\\B. (\\C. (\\D. (\\E. (\\F. (\\G. (\\H. (\\I. (\\J. (\\K. (\\L. (\\M. (\\N. (\\O. (\\P. (\\Q. (\\R. (\\S. (\\T. (\\U. (\\V. (\\W. (\\X. (\\Y. (\\Z. (\\a. (\\b. (\\c. (\\d. (\\e. (\\f. (\\g. (\\h. (\\i. (\\j. (\\k. (\\l. (\\m. (\\n. (\\o. (\\p. (\\q. (\\r. (\\s. (\\t. (\\u. (\\v. (\\w. (\\x. (\\y. (\\z. x))))))))))))))))))))))))))))))))))))))))))))))))))))"
    in
        let term_with_all_fv = "(((((((((((((((((((((((((((((((((((((((((((((((((((A B) C) D) E) F) G) H) I) J) K) L) M) N) O) P) Q) R) S) T) U) V) W) X) Y) Z) a) b) c) d) e) f) g) h) i) j) k) l) m) n) o) p) q) r) s) t) u) v) w) x) y) z)"
        in
            test_substitute_expected "x" term_with_all_fv term_with_all_variables "OutOfVariablesError";
    
    