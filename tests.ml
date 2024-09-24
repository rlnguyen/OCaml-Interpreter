open Expr ;;
open Evaluation ;;
open CS51Utils ;;
open Absbook ;;

(* Test ing toolkit *)
let var = "x" ;;
let var0 = "var0" ;; 
let var1 = "var1" ;;
let var2 = "var2" ;;

let num1 = Num 14 ;;
let num2 = Num 24 ;; 
let num3 = Num 70 ;;

let float1 = Float 3.5;;
let float2 = Float 1.5 ;;

let bool_true = Bool true ;;
let bool_false = Bool false ;;  

let unop = Unop (Negate, num1) ;; 
let bad_unop = Unop (Negate, bool_true) ;;

let binop_ints = Binop (Plus, num1, num3) ;; 
let binop_f1 = Binop (FloatPlus, float1, float2) ;;
let binop_f2 = Binop (FloatTimes, float1, float2) ;;
let binop_floats = Binop (GreaterThan, float1, float2) ;; 
let binop_bool1 = Binop (Equals, bool_true, bool_false) ;;
let binop_bool2 = Binop (LessThan, bool_true, bool_false) ;; 
let binop_comp_int = Binop (LessThan, num1, num2) ;; 
let binop_bad = Binop (Plus, bool_false, bool_true) ;; 
let binop_string = Binop (Concat, String ("Hello "), String ("world.")) ;; 

let cond_1 = Conditional (bool_true, num1, num2) ;; 
let cond_2 = Conditional (bool_false, num1, num2) ;;

let f1 = Fun (var, Binop (Plus, Var (var), num1)) ;; 
let f2 = Fun (var0, Conditional (Var (var0), num2, num3)) ;; 
let f3 = Fun (var1, Binop (Times, Var (var1), num1)) ;;

let let1 = Let ("f1", f1, App (Var("f1"), num2)) ;; 
let let2 = Let ("f2", f2, App (Var("f2"), bool_true)) ;; 

let concrete_tests () = 
    unit_test (exp_to_concrete_string (Var (var)) = "x") "exp_concrete Var";
    unit_test (exp_to_concrete_string num1 = "14") "exp_concrete Num";
    unit_test (exp_to_concrete_string bool_true = "true") "exp_concrete Bool";
    unit_test (exp_to_concrete_string unop = "~-14") "exp_concrete Unop";
    unit_test (exp_to_concrete_string binop_ints = "14 + 70") "exp_concrete Binop";
    unit_test (exp_to_concrete_string cond_1 = "if true then 14 else 24") 
        "exp_concrete Cond";
    unit_test (exp_to_concrete_string f1 = "fun x -> x + 14") "exp_concrete Fun";
    unit_test (exp_to_concrete_string let1 = 
                "Let f1 = fun x -> x + 14 in (f1) 24") "exp_concrete Let + App" ;;

let free_vars_tests () = 
    unit_test (free_vars (Num 2) = vars_of_list []) 
        "free_vars num";
    unit_test (free_vars (Var ("x")) = vars_of_list ["x"]) 
        "free_vars var x";
    unit_test (free_vars (Let ("f", Fun ("y", 
                                            Binop (Plus, Binop (Plus, Var ("x"), 
                                                                      Var ("z")), 
                                                         Var ("y"))), 
                                        App (Var ("f"), Var ("w")))) 
                = vars_of_list ["x"; "z"; "w"])
        "free_vars binop fun app let";
    unit_test (free_vars (Let ("x", 
                              Binop (Plus, Var ("x"), Num (2)), 
                              Binop (Plus, Var ("x"), Var ("y"))))
                = vars_of_list ["y"; "x"])
        "free_vars let";
    unit_test (free_vars (Let ("x", Fun ("y", Var ("x")), Var ("x")))
                = vars_of_list ["x"])
        "free vars let app";
    unit_test (free_vars (Letrec ("f", Fun ("x", Binop (Plus, 
                                                        Binop (Plus, Var ("x"), 
                                                        Var ("z")), 
                                                App (Var ("f"), Var ("y")))), 
                                                App (Var ("f"), Var ("l"))))
                = vars_of_list ["y"; "z"; "l"]) 
        "free_vars let rec";
    unit_test (free_vars (Conditional (Var ("f"), Var ("x"), Var ("y"))) 
                = vars_of_list ["f"; "x"; "y"])
        "free_vars conditional";;

let subst_tests () =
    unit_test (subst var num1 num3 = Num (70)) 
        "subst num (identical literals)";
    let init_sub1 = (subst "f" bool_true (Conditional (Var ("f"), Var ("x"), Var ("y")))) in
    unit_test (subst "y" num2 (subst "x" num1 init_sub1) 
                = Conditional (Bool (true), num1, num2))
        "subst conditional";
    unit_test (subst "f" f1 (App (Var ("f"), Num (14))) = App (f1, Num (14)))
        "subst app";
    unit_test (subst var num1 (Fun (var, Binop (Plus, Var (var), Num (14))))
                = Fun (var, Binop (Plus, Var (var), Num (14))))
        "subst fun base";
    unit_test (subst var num1 (Fun (var0, Binop (Plus, Var (var), Num (14))))
                = Fun (var0, Binop (Plus, num1, Num (14))))
        "subst fun 13.13";
    let init_sub2 = 
        subst "f" (Fun ("z", Var ("y"))) (App (Fun ("y", Binop (Plus, 
                                                                App (Var ("f"), 
                                                                    Num (3)), 
                                                                    Var ("y"))), 
                                               Num (1))) in
    unit_test (free_vars init_sub2
                = vars_of_list ["y"])
        "subst fun 13.14 app";
    unit_test (subst "x" num1 (Let ("x", Binop (Plus, Var ("x"), Num (14)), Var ("x")))
                = Let ("x", Binop (Plus, Num (14), Num (14)), Var ("x")))
        "let 13.15";;

let eval_s_tests () =
    let empty = Env.empty () in 
    unit_test (eval_s num1 empty = Env.Val (num1))
        "eval_s num & literals";
    unit_test (try 
                eval_s (Var ("x")) empty <> eval_s (Var ("x")) empty 
              with 
                EvalError (_) -> true | _ -> false)
        "eval_s unbound Var";
    unit_test (eval_s f1 empty = Env.Val (f1))
        "eval_s fun";
    unit_test (eval_s binop_ints empty = Env.Val (Num (84)))
        "eval_s binop";
    unit_test (eval_s binop_f1 empty = Env.Val (Float (5.0)))
        "eval_s binop_float";
    unit_test (eval_s binop_string empty = Env.Val (String ("Hello world.")))
        "eval_s binop concat string";
    unit_test (try 
                eval_s binop_bad empty <> eval_s binop_bad empty 
              with 
                EvalError (_) -> true | _ -> false)
        "eval_s binop fail";
    unit_test (eval_s let1 empty = Env.Val (Num (38)))
        "eval_s let app";
    unit_test (try
                eval_s (App (Num (4), Num (3))) empty <> eval_s 
                (App (Num (4), Num (3))) empty
              with
                EvalError (_) -> true | _ -> false) 
        "eval_s failed app";;

let env_tests () =
    let empty = Env.empty () in 
    unit_test (try 
                Env.lookup empty "null" <> Env.lookup empty "null" 
              with 
                EvalError (_) -> true | _ -> false)
        "lookup failed";
    unit_test (Env.value_to_string (Env.Closure (Num (3), empty)) 
                = "Closure (Val = 3, Env : {})")
        "closure with env";
    unit_test (Env.value_to_string ~printenvp: 
                false (Env.Closure (Num (3), empty)) 
                = "Closure (Val = 3, Env : {})")
        "closure without env";

    let test_env = 
        Env.extend (Env.extend empty "x" (ref (Env.Val (Num 5)))) 
        "y" (ref (Env.Val (Num 15))) in
    unit_test (Env.env_to_string test_env = "{x ↦ 5;y ↦ 15;}")
        "env_to_string reg env extend";
    unit_test (Env.lookup test_env "x" = Env.Val (Num 5))
        "lookup1" ;

    let test_env2 = Env.extend test_env "x" (ref (Env.Val (Num 25))) in 
    unit_test (Env.env_to_string test_env2 = "{y ↦ 15;x ↦ 25;}")
        "extend override";
    unit_test (Env.lookup test_env2 "x" = Env.Val (Num 25))
        "lookup2" ;;

let eval_d_tests () = 
    let empty = Env.empty () in 
    unit_test (eval_d num1 empty = Env.Val (num1))
        "eval_d literals";
    unit_test (try 
                eval_d (Var ("x")) empty <> eval_d (Var ("x")) empty 
                with EvalError (_) -> true | _ -> false)
        "eval_d unbound variable";
    unit_test (eval_d cond_1 empty = Env.Val (num1))
        "eval_d conditional";
    unit_test (eval_d f1 empty = Env.Val (f1))
        "eval_d fun";
    unit_test (eval_d binop_ints empty = Env.Val (Num (84)))
        "eval_d binop plus";
    unit_test (eval_d binop_f1 empty = Env.Val (Float (5.0)))
        "eval_d binop_float plus";
    unit_test (eval_d binop_f2 empty = Env.Val (Float (5.25)))
        "eval_d binop_float times";
    unit_test (eval_d binop_string empty = Env.Val (String ("Hello world.")))
        "eval_d binop concat";
    unit_test (try 
                eval_d binop_bad empty <> eval_d binop_bad empty 
              with EvalError (_) -> true | _ -> false)
        "eval_d Binop fail";
    unit_test (eval_d let1 empty = Env.Val (Num (38)))
        "eval_d let + app";
    unit_test (eval_d (Let ("x", Num (8), 
                       Let ("f", Fun ("y", Binop (Plus, Var ("x"), Var ("y"))), 
                       Let ("x", Num (5), App (Var ("f"), Num (5)))))) 
                       empty
                = Env.Val (Num 10))
        "eval_d dynamic";;
    
let tests () =
  concrete_tests ();
  free_vars_tests ();
  subst_tests ();
  eval_s_tests ();
  env_tests ();
  eval_d_tests ();

  () ;;

let _ = tests () ;;