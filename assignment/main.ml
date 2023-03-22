(* Elementary types *)
type expr =
  | EChar of char
  | EInt of int
  | EBool of bool
  | Var of string
  (* needed only to define singleton lists *)
  | ESingleList of expr
  (* kinda: EList:= expr * EList | expr * expr (last element of the list) *)
  | EList of expr * expr
  (* == Commands == *)
  | Let of string * expr
  | LetIn of string * expr * expr
  | Prim of string * expr * expr
  | If of expr * expr * expr
  | Fun of string * expr
  | Call of expr * expr
  | FunR of string * string * expr
  | Letrec of string * string * expr * expr
  | CSeq of expr * expr

(* Environment definition: association list, i.e., a list of pair (identifier, data) *)
type 'v env = (string * 'v) list

(* Runtime value definition (boolean are encoded as integers) *)
type value =
  (* == Values == *)
  | Char of char
  | Int of int
  | Transition of int * char * int
  | VList of value list
  (* == Closures == *)
  | Closure of string * expr
  | RecClosure of string * string * expr

(* Function to return data bounded to {x} in the environment *)
let rec lookup env x =
  match env with
  | [] -> failwith (x ^ "not found")
  | (y, v) :: r -> if x = y then v else lookup r x

(* === Interpreter === *)
let rec eval (e : expr) (env : (string * value) list) : (value * (string * value) list) =
  match e with
  | EChar c -> (Char c, env)
  | EInt n -> (Int n, env)
  | EBool n -> let n_int = if n then Int 1 else Int 0 in (n_int, env)
  | Var x -> (lookup env x, env)
  | ESingleList (e1) -> let e1_value, env = eval e1 env in (VList [e1_value], env)
  | EList (e1, e2) ->
      (* Internal function to create an `OCaml list` from a sequence of `VList` *)
      let rec evaluate_list e =
        match e with
          | EList (e3, e4) -> let eval1, env = eval e3 env in eval1 :: evaluate_list e4
          | e_last -> let eval1, env = eval e_last env in [ eval1 ]
        in
          (VList (evaluate_list e), env)

  | Let (s, e1) ->
      let let_value, env = eval e1 env in let env_upd = (s, let_value) :: env in (let_value, env_upd)
  | LetIn (s, e1, e2) ->
      let let_value, env = eval e1 env in
        let env_upd = (s, let_value) :: env in
          (* We do not keep env_upd after evaluating in_value *)
          let in_value, _ = eval e2 env_upd in (in_value, env)

  | Prim (op, e1, e2) -> (
      let v1, env = eval e1 env in
      let v2, env = eval e2 env in
        match (op, v1, v2) with
        | "*", Int i1, Int i2 -> (Int (i1 * i2), env)
        | "+", Int i1, Int i2 -> (Int (i1 + i2), env)
        | "-", Int i1, Int i2 -> (Int (i1 - i2), env)
        | "=", Int i1, Int i2 -> (Int (if i1 = i2 then 1 else 0), env)
        | "<", Int i1, Int i2 -> (Int (if i1 < i2 then 1 else 0), env)
        | ">", Int i1, Int i2 -> (Int (if i1 > i2 then 1 else 0), env)
        | _, _, _ -> failwith "Unexpected primitive.")

  | If (e1, e2, e3) -> (
      let v1, env = eval e1 env 
      in
        match v1 with
        | Int 1 -> eval e2 env 
        | Int 0 -> eval e3 env
        | _ -> failwith "Unexpected condition.")
  | CSeq (e1, e2) ->
    let e1_value, env_upd = eval e1 env in
    eval e2 env_upd 

  | Fun (f_param, f_body) -> (Closure (f_param, f_body), env)
  | FunR (rec_f_name, f_param, f_body) -> (RecClosure(rec_f_name, f_param, f_body), env)
  | Letrec (rec_f_name, f_param, f_body, let_body) ->
      let rval, env = eval (FunR(rec_f_name, f_param, f_body)) env in
      let env_upd = (rec_f_name, rval)::env in
      eval let_body env_upd

  | Call (f_name, param) -> 
    let f_closure, env = eval f_name env in
    begin
      match f_closure with
      | Closure (f_param, f_body) ->
          let f_param_val, env = eval param env in
          let env_upd = (f_param, f_param_val) :: env in
          eval f_body env_upd
      | RecClosure(rec_f_name, f_param, f_body) ->
          let f_param_val, env = eval param env in
          let env_upd = (rec_f_name, f_closure)::(f_param, f_param_val)::env in
          eval f_body env_upd
      | _ -> failwith "Function unknown"
    end
;;
