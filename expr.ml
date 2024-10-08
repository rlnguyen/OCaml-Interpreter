(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Concat
  | Plus
  | FloatPlus
  | Minus
  | FloatMinus
  | Times
  | FloatTimes
  | Equals
  | GreaterThan
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | String of string                     (* strings *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var v -> SS.singleton v
  | Unop (_, e) -> free_vars e                 
  | Binop (_, e1, e2)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) ->  
    SS.union (SS.union (free_vars e1) (free_vars e2)) (free_vars e3)
  | Fun (v, e) -> SS.remove v (free_vars e)        
  | Let (v, e1, e2) -> SS.union (SS.remove v (free_vars e2)) (free_vars e1)
  | Letrec (v, e1, e2) -> 
    SS.union (SS.remove v (free_vars e2)) (SS.remove v (free_vars e1))
  | _ -> SS.empty ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no other variable names
   use the prefix "var". (Otherwise, they might accidentally be the
   same as a generated variable name.) *)
   let new_varname : unit -> varid =
    let i = ref 0 in
    fun () ->
    i := !i + 1;
    "var" ^ string_of_int (!i - 1) ;;

(*......................................................................
  Substitution
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  if SS.mem var_name (free_vars exp) then
    let sub = subst var_name repl in 
    match exp with
    | Num x -> Num x
    | Float x -> Float x
    | String s -> String s
    | Bool b -> Bool b
    | Raise -> Raise
    | Unassigned -> Unassigned 
    | Var v -> if v = var_name then repl else Var v
    | Unop (u, e) -> Unop (u, sub e)
    | Binop (b, e1, e2) -> Binop (b, sub e1, sub e2)
    | App (f, e) -> App (sub f, sub e)
    | Conditional (e1, e2, e3) -> Conditional (sub e1, sub e2, sub e3)
    | Fun (v, e) ->
      if var_name = v then exp
      else if SS.mem var_name (free_vars exp) then let new_v = new_varname () in
      Fun (new_v, subst var_name repl (subst v (Var new_v) e))
      else Fun (v, subst var_name repl e)
    | Let (v, e1, e2) -> 
      if v = var_name then 
        Let (v, sub e1, e2)
      else if SS.mem v (free_vars repl) then
        let z = new_varname () in
        Let (z, sub e1, sub (subst v (Var z) e2))
      else
        Let (v, sub e1, sub e2)
    | Letrec (v, e1, e2) -> 
      if v = var_name then 
        Letrec (v, sub e1, e2)
      else if SS.mem v (free_vars repl) then
        let z = new_varname () in
        Letrec (z, sub e1, sub (subst v (Var z) e2))
      else
        Letrec (v, sub e1, sub e2)
    else
      exp
   ;;
     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)

let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Float f -> string_of_float f
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b 
  | String s -> "\"" ^ s ^ "\"" 
  | Unop (_, e) -> "~-" ^ exp_to_concrete_string e                
  | Binop (b, e1, e2) -> 
    let arg1 = exp_to_concrete_string e1 in 
    let arg2 = exp_to_concrete_string e2 in                     
    (match b with
    | Concat -> arg1 ^ " ^ " ^ arg2
    | Plus -> arg1 ^ " + " ^ arg2
    | FloatPlus -> arg1 ^ " +. " ^ arg2
    | Minus -> arg1 ^ " - " ^ arg2
    | FloatMinus  -> arg1 ^ " -. " ^ arg2
    | Times -> arg1 ^ " * " ^ arg2
    | FloatTimes -> arg1 ^ " *. " ^ arg2
    | Equals -> arg1 ^ " = " ^ arg2
    | GreaterThan -> arg1 ^ " > " ^ arg2
    | LessThan -> arg1 ^ " < " ^ arg2)
  | Conditional (e1, e2, e3) ->  "if " ^ exp_to_concrete_string e1 ^
                                 " then " ^ exp_to_concrete_string e2 ^ 
                                 " else " ^ exp_to_concrete_string e3
  | Fun (v, e) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string e                
  | Let (v, e1, e2) -> 
    "Let " ^ v ^ " = " ^ exp_to_concrete_string e1 
               ^ " in " ^ exp_to_concrete_string e2
  | Letrec (v, e1, e2) -> 
    "Let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 
                   ^ " in " ^ exp_to_concrete_string e2
  | Raise -> "Raise exception"
  | Unassigned -> "Unassigned"
  | App (f, e) -> 
    "(" ^ exp_to_concrete_string f ^ ") " ^ exp_to_concrete_string e ;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var ("^ v ^ ")"
  | Float x -> "Float (" ^ string_of_float x ^ ")"
  | Num n -> "Num (" ^ string_of_int n ^ ")"
  | Bool b -> "Bool (" ^ string_of_bool b ^ ")"  
  | String s -> "String (" ^ s ^ ")"
  | Unop (_, e) -> "Unop (Negate, " ^ exp_to_concrete_string e ^ ")"    
  | Binop (operator, arg1, arg2) ->
    let make_str op_s = "Binop(" ^ op_s ^ ", " ^  exp_to_abstract_string arg1 ^
                        ", " ^ exp_to_abstract_string arg2 ^ ")" in
    (match operator with
    | Concat -> "Concat"
    | Plus -> "Plus"
    | FloatPlus -> "Float Plus"
    | Minus -> "Minus"
    | FloatMinus -> "Float Minus"
    | Times -> "Times"
    | FloatTimes -> "Float Times"
    | Equals -> "Equals"
    | GreaterThan -> "Greater Than"
    | LessThan -> "Less Than")
  | Conditional (a, arg1, arg2) ->
    "Conditional(" ^ (exp_to_abstract_string a) ^ ", " ^
    (exp_to_abstract_string arg1) ^ ", " ^ (exp_to_abstract_string arg2) ^ ")"
  | Fun (v, e) -> "Fun(" ^ v ^ ", " ^ exp_to_abstract_string e ^ ")"
  | Let (v, e1, e2) ->
    "Let(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^
    exp_to_abstract_string e2 ^ ")"
  | Letrec (v, e1, e2) ->
    "Letrec(" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^
    exp_to_abstract_string e2 ^ ")"
  | Raise -> "Raise exception"
  | Unassigned -> "Unassigned"
  | App (f, e) -> "App (" ^ exp_to_abstract_string f ^ ", " 
                          ^ exp_to_abstract_string e ^ ")";;

