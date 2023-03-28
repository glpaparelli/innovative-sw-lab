(* AST *)
type expr =
  | EChar of char
  | EInt of int
  | EBool of bool
  | Var of string

  | LetIn of string * expr * expr               (* let x = e1 in e2 *)
  | Prim of string * expr * expr                (* binop e1 e2 *)
  | If of expr * expr * expr                    (* if e1 then e2 else e3 *)
  | Fun of string * expr                        (* param identifier * funct body *)
  | Call of expr * expr                         (* funct identifier * param *)
  | FunR of string * string * expr              (* rec funct identifier * param identifier * funct body *)
  | Letrec of string * string * expr * expr     (* let rec f x = e1 in e2 *)

  | GetInput of int                             (* stub function: integers from stdin *)

(* environment definition: a list of triplets <variable, value, taintness> *)
type 'v env = (string * 'v * bool) list

(* runtime value definition (boolean are encoded as integers) *)
type value =
  | Char of char
  | Int of int
  | Bool of bool

  | Closure of string * expr
  | RecClosure of string * string * expr

(* function to return the value of the variable {x} *)
let rec lookup env x =
  match env with
  | [] -> failwith (x ^ "not found")
  | (y, v, _) :: r -> if x = y then v else lookup r x

(* function to return the taintness of a variable *)
let rec t_lookup env x = 
  match env with
  | [] -> failwith (x ^ "not found")
  | (y, _, t) :: r -> if x = y then t else t_lookup r x

(* ------------------------------------ Interpreter ------------------------------------ *)

(* 
  Taintness is introduced only by the stub function GetInput and it is propagated during the 
  execution of the program. 
  The taintness here is "bounded" to the single expression: the eval function returns a triple 
  <value v, environment, taintness of v>. 
  This is necessary for the propagation of the taintness. 
  
  For exucuting GetInput(n) + 5 (that has taintness = true) we have to evaluate GetInput(n) and 5
  sperately and get the value and taintness status of each to comute the resultant taintness.

  The environment env is an association list <identifier, value, taintness of identifier> 
  so that we can keep track of the taintness of identifiers and then propragate accordingly. 
  (e.g.: expr: let x = GetInput(n), x will have tainted status = true in the env, and the expr will
  return a triple <n, env, true>)
*)

let rec eval (e : expr) (env : (string * value * bool) list) : value * ((string * value * bool) list) * bool =
  match e with
  | EChar c -> (Char c, env, false)
  | EInt n -> (Int n, env, false)
  | EBool b -> (Bool b, env, false)

  | Var x -> (lookup env x, env, t_lookup env x)

  | Prim (op, e1, e2) -> 
    begin
      let v1, env, t1 = eval e1 env in
      let v2, env, t2 = eval e2 env in
        match (op, v1, v2) with
        (* taintness of binary ops is given by the OR of the taintness of the args *)
        | "*", Int i1, Int i2 -> (Int (i1 * i2), env, t1 || t2)
        | "+", Int i1, Int i2 -> (Int (i1 + i2), env, t1 || t2)
        | "-", Int i1, Int i2 -> (Int (i1 - i2), env, t1 || t2)
        | "=", Int i1, Int i2 -> (Bool (if i1 = i2 then true else false), env, t1 || t2)
        | "<", Int i1, Int i2 -> (Bool (if i1 < i2 then true else false), env, t1 || t2)
        | ">", Int i1, Int i2 -> (Bool (if i1 > i2 then true else false), env, t1 || t2)
        | _, _, _ -> failwith "Unexpected primitive."
    end

  | LetIn (s, e1, e2) ->
      let v1, env, t1 = eval e1 env in
        let env' = (s, v1, t1) :: env in
          (* we do not keep env' after evaluating v2 *)
          let v2, _, t2 = eval e2 env' in (v2, env, t2)

  | If (e1, e2, e3) -> 
      begin
        let v1, env, t1 = eval e1 env in
        match v1 with
          | Bool true -> eval e2 env 
          | Bool false -> eval e3 env
          | _ -> failwith "Unexpected condition."
      end

  (* taintness of function depends only on the parameters on which they will be applied *)
  | Fun (f_param, f_body) -> (Closure (f_param, f_body), env, false)
  | FunR (f_name, f_param, f_body) -> (RecClosure(f_name, f_param, f_body), env, false)
  
  (*
    when defining a recursive function and then using the same function in the
    "in" part there is the need of an env update: let rec f x = f_body in let_body, f is in 
    the "let_body" and f is an unknown identifier in the current env, since it is
    defined just now
  *)
  | Letrec (f_name, f_param, f_body, let_body) ->
      let rval, env, _ = eval (FunR(f_name, f_param, f_body)) env in
      let env' = (f_name, rval, false)::env in
      eval let_body env'

  (* functions are always executed, even on tainted arguments *)
  | Call (f_name, param) -> 
    let f_closure, env, _ = eval f_name env in
    begin
      match f_closure with
      | Closure (f_param, f_body) ->
          let f_param_val, env, f_param_t = eval param env in
          let env' = (f_param, f_param_val, f_param_t) :: env in
          eval f_body env'
      | RecClosure(f_name, f_param, f_body) ->
          let f_param_val, env, f_param_t = eval param env in
          let env' = (f_name, f_closure, false)::(f_param, f_param_val, f_param_t)::env in
          eval f_body env'
      | _ -> failwith "Function unknown"
    end

  (* the input from the user is always considered tainted *)
  | GetInput(n) -> (Int n, env, true)

(* ----------------------------------------- Tests ----------------------------------------- *)
open Printf

(* ---- HO Test ---- *)
(* here the let is used for simplicity in order to make apply_f more readable *)
let times2 = Fun ("x", Prim ("*", Var "x", EInt 2))
let apply_f = LetIn(
  "apply", 
  Fun("f", Fun("x", Call(Var("f"), Var("x")))), 
  Call(Call(Var("apply"), times2), EInt 4)
)
let ho_test() = 
  match eval apply_f [] with 
  | Int v, _, _ -> printf("HO Test -> expected: 8 | obtained: %d\n") v
  |  _ -> print_endline "" 

(* Taintness Tests *)
let untainted_let = LetIn("x", Prim("*", EInt(2), EInt(2)), Prim("+", Var("x"), EInt(1)))
let test1() =
  match eval untainted_let [] with
  | (Int v, env, t) -> printf("Taint Test 1 -> expected: 5, false | obtained: %d, %b\n") v t
  | _ -> print_endline "" 

let tainted_let = LetIn("x", GetInput(4), Prim("+", Var("x"), EInt(1)))
let test2() =
  match eval tainted_let [] with
  | (Int v, env, t) -> printf("Taint Test 2 -> expected: 5, true | obtained: %d, %b\n") v t
  | _ -> print_endline "" 

let plus5 = Fun("y", Prim ("+", Var "y", EInt 5))
let f_taint = LetIn(
  "f_taint", 
  Fun("f", Fun("x", Call(Var("f"), Var("x")))), 
  Call(Call(Var("f_taint"), plus5), GetInput(4))
)
let test3() = 
    match eval f_taint [] with
    | (Int v, env, t) -> printf("Taint Test 3 -> expcted: 9, true | obtained: %d, %b\n") v t
    | _ -> print_endline "" 


let main() = ho_test(), test1(), test2(), test3();;