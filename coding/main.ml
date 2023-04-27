(* LIS Assignment: Interpreter /w Taint Analysis *)

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
  | Call of expr * expr                         (* fun identifier * param *)
  | FunR of string * string * expr              (* rec fun identifier * param identifier * fun body *)

  | GetInput of expr                             (* function that takes input, taint source*)

(* environment definition: a list of triplets <variable, value, taintness> *)
type 'v env = (string * 'v * bool) list

(* runtime value definition *)
type value =
  | Char of char
  | Int of int
  | Bool of bool

  | Closure of string * expr * value env
  | RecClosure of string * string * expr * value env

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
  the eval takes the expression to be evaluated, the environment and a taintness status,
  this is needed since GetInput can pass an expression, and we need a way to keep the taintness 
  status as we traverse the unsafe expression. 

  The eval types (Char, Int, Bool and Closures) are considered tainted (t = true) when they
  are passed from the GetInput function. 
  This is in accordance with the paper, where "any program value whose computation depends 
  on data derived from a tainted source is considered tainted"
*)

let rec eval (e : expr) (env:value env) (t : bool) : value * bool =
  match e with
  | EChar c -> (Char c, t)
  | EInt n -> (Int n, t)
  | EBool b -> (Bool b, t)

  | Var x -> (lookup env x, t_lookup env x)

  | Prim (op, e1, e2) -> 
    begin
      let v1, t1 = eval e1 env t in
      let v2, t2 = eval e2 env t in
        match (op, v1, v2) with
        (* taintness of binary ops is given by the OR of the taintness of the args *)
        | "*", Int i1, Int i2 -> (Int (i1 * i2), t1 || t2)
        | "+", Int i1, Int i2 -> (Int (i1 + i2), t1 || t2)
        | "-", Int i1, Int i2 -> (Int (i1 - i2), t1 || t2)
        | "=", Int i1, Int i2 -> (Bool (if i1 = i2 then true else false), t1 || t2)
        | "<", Int i1, Int i2 -> (Bool (if i1 < i2 then true else false), t1 || t2)
        | ">", Int i1, Int i2 -> (Bool (if i1 > i2 then true else false), t1 || t2)
        | _, _, _ -> failwith "Unexpected primitive."
    end

  (* let i = e1 in e2 *)
  | LetIn (i, e1, e2) ->
      let v1, t1 = eval e1 env t in
        let env' = (i, v1, t || t1)::env in
          eval e2 env' t

  (* 
    we compute the value and taintness of the guard. the taintness status of the whole 
    If is given by the OR of the taintness of the guard and the taintness of executed 
    branch expression. 
    in summary, we consider tainted the result of an If producted by either a tainted guard or 
    branch 
  *)
  | If (e1, e2, e3) -> 
      begin
        let v1, t1 = eval e1 env t in
        match v1 with
          | Bool true -> let v2, t2 = eval e2 env t in (v2, t1 || t2)
          | Bool false -> let v3, t3 = eval e3 env t in (v3, t1 || t3)
          | _ -> failwith "Unexpected condition."
      end

  | Fun (f_param, f_body) -> (Closure (f_param, f_body, env), t)
  | FunR (f_name, f_param, f_body) -> (RecClosure(f_name, f_param, f_body, env), t)

  (* 
    we compute the result of the application of the function, the taintness
    status is given by the OR of the taintness of the function itself, the
    taintness status of the parameter on which the function is applied and the
    taintness status of the result of the function (as the body could be tainted)
  *)
  | Call (f_name, param) -> 
    let f_closure, f_t = eval f_name env t in
    begin
      match f_closure with
      | Closure (f_param, f_body, f_dec_env) ->
          let f_param_val, f_param_t = eval param env t in
            let env' = (f_param, f_param_val, f_param_t)::f_dec_env in
              let f_res, t_res = eval f_body env' t
                in (f_res, f_t || f_param_t || t_res)
      
      | RecClosure(f_name, f_param, f_body, f_dec_env) ->
          let f_param_val, f_param_t = eval param env t in
            let env' = (f_name, f_closure, f_t)::(f_param, f_param_val, f_param_t)::f_dec_env in
              let f_res, t_res = eval f_body env' t
                in (f_res, f_t || f_param_t || t_res)

      | _ -> failwith "Function unknown"
    end

  (* we set the taint "flag" true, while we evaluate the expr e the taintness status of 
     the value will be true *)
  | GetInput(e) -> eval e env true

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
let test0() = 
  match eval apply_f [] false with 
  | Int v, _ -> printf("HO Test -> expected: 8 | obtained: %d\n") v
  |  _ -> print_endline "test 0 failed" 

(* Taintness Tests *)
let untainted_let = LetIn("x", Prim("*", EInt(2), EInt(2)), Prim("+", Var("x"), EInt(1)))
let test1() =
  match eval untainted_let [] false with
  | (Int v, t) -> printf("Untainted Let Test -> expected: 5, false | obtained: %d, %b\n") v t
  | _ -> print_endline "test 1 failed" 

let tainted_let = LetIn("x", GetInput(EInt(4)), Prim("+", Var("x"), EInt(1)))
let test2() =
  match eval tainted_let [] false with
  | (Int v, t) -> printf("Tainted Let Test -> expected: 5, true | obtained: %d, %b\n") v t
  | _ -> print_endline "test 2 failed" 

(* GetInput tests *)

(* form input we get a (tainted) function *)
let f_from_input = GetInput(times2)
let tainted_f_input = LetIn(
  "f", 
  f_from_input,
  Call(Var("f"), EInt(5))
)
let test3() = match eval tainted_f_input [] false with
  | (Int v, t) -> printf("Tainted Function Test -> expcted: 10, true | obtained: %d, %b\n") v t
  | _ -> print_endline "test 3 failed" 

(* from input we get a tainted parameter and then we apply an untainted function *)
let tainted_param = LetIn(
  "f", 
  times2, 
  Call(Var("f"), GetInput(EInt(5)))
)
let test4() = match eval tainted_param [] false with
  | (Int v, t) -> printf("Tainted Parameter Test -> expcted: 10, true | obtained: %d, %b\n") v t
  | _ -> print_endline "test 4 failed" 

(* from input we get a whole expr = If *)
let tainted_if = GetInput(If(Prim(">", EInt(2), EInt(0)), EBool(true), EBool(false)))
let test5() = match eval tainted_if [] false with
  | (Bool v, t) -> printf("Tainted If Test -> expcted: true, true | obtained: %b, %b\n") v t
  | _ -> print_endline "test 5 failed"

(* classic untainted if test *)
let untainted_if = If(
  Prim(">", EInt(2), EInt(0)), 
  EBool(true), 
  EBool(false))
let test6() = match eval untainted_if [] false with
  | (Bool v, t) -> printf("Untainted If Test -> expcted: true, false | obtained: %b, %b\n") v t
  | _ -> print_endline "test 6 failed"

(* an If with a branch from the user (tainted) *)
let tainted_if_branch = If(
  Prim(">", EInt(2), EInt(0)), 
  GetInput(EBool(true)), 
  EBool(false))
let test7() = match eval tainted_if_branch [] false with
  | (Bool v, t) -> printf("Tainted If Branch Test -> expcted: true, true | obtained: %b, %b\n") v t
  | _ -> print_endline "test 7 failed"

let main() = test0(), test1(), test2(), test3(), test4(), test5(), test6(), test7();;