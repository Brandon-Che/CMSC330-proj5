open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> None
  | (var, value) :: t -> if x = var then Some value else lookup t x

let rec optimize env e = 
  match e with 
  | Int(i) -> Int(i)
  | Bool(b) -> Bool(b)
  | ID(s) -> 
    (match (lookup env s) with
    | None -> ID(s)
    | Some(e) -> e)
  | Not(e1) -> 
    let e1 = optimize env e1 in
    (match e1 with
    | Bool(b) -> Bool(not b)
    | _ -> Not(e1))
  | Binop(op, e1, e2) ->
    let e1 = optimize env e1 in
    let e2 = optimize env e2 in
    (match op with
    | Add -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Int(a + b)
      | ID(a), Int(b) -> if b = 0 then ID(a) else Binop(Add, e1, e2)
      | Int(a), ID(b) -> if a = 0 then ID(b) else Binop(Add, e1, e2)
      | _ -> Binop(Add, e1, e2))
    | Sub -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Int(a - b)
      | ID(a), Int(b) -> if b = 0 then ID(a) else Binop(Sub, ID(a), Int(b))
      | _ -> Binop(Sub, e1, e2))
    | Mult -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Int(a * b)
      | ID(a), Int(b) -> if b = 0 then Int(0) else if b = 1 then ID(a) else Binop(Mult, ID(a), Int(b))
      | Int(a), ID(b) -> if a = 0 then Int(0) else if a = 1 then ID(b) else Binop(Mult, Int(a), ID(b))
      | _ -> Binop(Mult, e1, e2))
   | Div -> 
      (match e1, e2 with
      | Int(a), Int(b) -> if b = 0 then raise (DivByZeroError) else Int(a/b)
      | ID(a), Int(b) -> if b = 0 then raise (DivByZeroError) else if b = 1 then ID(a) else Binop(Div, ID(a), Int(b))
      | Int(a), ID(b) -> if a = 0 then Int(0) else Binop(Div, Int(a), ID(b))
      | _ -> Binop(Div, e1, e2))
    | Greater -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a > b)
      | _ -> Binop(Greater, e1, e2))
    | GreaterEqual -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a >= b)
      | _ -> Binop(GreaterEqual, e1, e2))
    | Less -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a < b)
      | _ -> Binop(Less, e1, e2))
    | LessEqual -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a <= b)
      | _ -> Binop(LessEqual, e1, e2))
    | Equal -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a = b)
      | _ -> Binop(Equal, e1, e2))
    | NotEqual -> 
      (match e1, e2 with
      | Int(a), Int(b) -> Bool(a <> b)
      | _ -> Binop(NotEqual, e1, e2))
    | Or ->
      (match e1, e2 with
      | Bool(a), Bool(b) -> Bool(a || b)
      | ID(a), Bool(b) -> if b then Bool(true) else Binop(Or, ID(a), Bool(b))
      | Bool(a), ID(b) -> if a then Bool(true) else Binop(Or, Bool(a), ID(b))
      | _ -> Binop(Or, e1, e2))
    | And ->
      (match e1, e2 with
      | Bool(a), Bool(b) -> Bool(a && b)
      | ID(a), Bool(b) -> if (not b) then Bool(false) else Binop(And, ID(a), Bool(b))
      | Bool(a), ID(b) -> if (not a) then Bool(false) else Binop(And, Bool(a), ID(b))
      | _ ->  Binop(And, e1, e2))
    | _ -> raise (TypeError("not an op")))
  | If(e1, e2, e3) -> 
    let e1 = optimize env e1 in
    let e2 = optimize env e2 in
    let e3 = optimize env e3 in
    (match e1 with
    | Bool(b) -> if b then e2 else e3
    | _ -> If(e1, e2, e3))
  | Let(v, e1, e2) -> 
    let new_env = (extend env v e1) in
    let e2 = optimize new_env e2 in
    optimize new_env e2
  | LetRec(v, expt, e1, e2) -> 
    let e1 = optimize env e1 in
    let e2 = optimize env e2 in
    LetRec(v, expt, e1, e2)
  | Fun(var, expt, e1) -> 
    let e1 = optimize env e1 in 
    (match lookup env var with 
    | None -> Fun(var, expt, e1)
    | Some(e) -> e1)
  | App(e1, e2) -> 
    (match e1 with 
    | Fun(var, expt, expr) -> 
      let e2 = optimize env e2 in
      let new_env = extend env var e2 in 
      optimize new_env e1
    | _ -> App(optimize env e1, optimize env e2))
  | Select(lab, e1) -> 
    let e1 = optimize env e1 in
    (match e1 with
    | Record(lst) -> 
      let rec search l = 
        (match l with
        | (lab2, exp)::t -> if lab2 = lab then exp else search t
        | [] -> raise (SelectError("not in record"))) in
      search lst
    | _ -> raise(SelectError("not a record")))
  | Record(lst) -> 
    let rec helper l = 
      match l with
      | [] -> []
      | (lab, exp)::t -> (lab, (optimize env exp))::(helper t) in
    Record(helper lst)
  | _ -> e