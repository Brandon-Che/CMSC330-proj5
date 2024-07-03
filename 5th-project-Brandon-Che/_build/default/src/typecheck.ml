open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound type for " ^ x))
  | (var, value) :: t -> if x = var then value else lookup t x

let rec is_subtype t1 t2 = 
if t1 = t2 then true else
  match t1, t2 with
  | TArrow(a,b), TArrow(c,d) -> (is_subtype a c) && (is_subtype b d)
  | TRec(l1), TRec(l2) -> 
    let rec is_in lst x exp = 
     ( match lst with 
      | [] -> false 
      | (lab, expt)::t -> if lab = x && (is_subtype expt exp) then true else (is_in t x exp)
      | _ -> raise (InvalidInputException("not right"))) in
    let rec helper lst1 lst2 = 
      (match lst1, lst2 with
      | _, [] -> true
      | _, (lab, expt)::t -> if is_in lst1 lab expt then helper lst1 t else false
      | _ -> raise (InvalidInputException("not right"))) in
    helper l1 l2
  | _ -> false

let rec typecheck (gamma: Ast.exptype environment) e = 
  match e with
  | Int(a) -> TInt
  | Bool(b) -> TBool
  | ID(i) -> lookup gamma i
  | Binop(op, e1, e2) -> 
    let t1 = typecheck gamma e1 in
    let t2 = typecheck gamma e2 in
    (match op with
    | Add -> if t1 = TInt && t2 = TInt then TInt else raise (TypeError ("Expected Ints"))
    | Sub -> if t1 = TInt && t2 = TInt then TInt else raise (TypeError ("Expected Ints"))
    | Mult -> if t1 = TInt && t2 = TInt then TInt else raise (TypeError ("Expected Ints"))
    | Div -> if t1 = TInt && t2 = TInt then TInt else raise (TypeError ("Expected Ints"))  
    | Greater -> if t1 = TInt && t2 = TInt then TBool else raise (TypeError ("Expected Ints"))  
    | GreaterEqual -> if t1 = TInt && t2 = TInt then TBool else raise (TypeError ("Expected Ints"))  
    | Less -> if t1 = TInt && t2 = TInt then TBool else raise (TypeError ("Expected Ints"))  
    | LessEqual -> if t1 = TInt && t2 = TInt then TBool else raise (TypeError ("Expected Ints"))  
    | Equal -> if t1 = t2 then TBool else raise (TypeError ("Expected same type"))  
    | NotEqual -> if t1 = t2 then TBool else raise (TypeError ("Expected same type"))  
    | And -> if t1 = TBool && t2 = TBool then TBool else raise (TypeError ("Expected Bools"))  
    | Or -> if t1 = TBool && t2 = TBool then TBool else raise (TypeError ("Expected Bools"))  
    | _ -> raise (TypeError ("Not an op")))
  | Not(e1) -> if (typecheck gamma e1) = TBool then TBool else raise (TypeError ("Expected Bool"))
  | If(e1, e2, e3) -> 
    let t1 = typecheck gamma e1 in
    let t2 = typecheck gamma e2 in
    let t3 = typecheck gamma e3 in
    if t1 = TBool then if t2 = t3 then t2 else raise (TypeError ("Expected same type")) else raise (TypeError ("Expected Bool"))
  | Fun(v1, expt, e1) ->
    let new_gamma = extend gamma v1 expt in
    TArrow (expt, (typecheck new_gamma e1))
  | App(e1, e2) -> 
    let t1 = typecheck gamma e1 in
    let t2 = typecheck gamma e2 in
    (match t1 with
    | TArrow(r, r') -> if is_subtype t2 r then r' else raise (TypeError("App error"))
    | _ -> raise (InvalidInputException("not right")))
  | Record(lst) -> 
    let rec helper l = 
      (match l with 
      | [] -> []
      | (lab, e1)::t -> (lab, (typecheck gamma e1))::(helper t)
      | _ -> raise (InvalidInputException("not right"))) in
    TRec(helper lst)
  | Select(lab, e1) -> 
    let t1 = typecheck gamma e1 in
    let rec search lst = 
      (match lst with
      | [] -> raise (InvalidInputException("not in record"))
      | (l, expt)::t -> if l = lab then expt else search t
      | _ -> raise (InvalidInputException("not right"))) in
    (match t1 with
    | TRec(lst) -> search lst
    | _ -> raise (InvalidInputException("not right")))
  | Let(v1, e1, e2) -> 
    let t1 = typecheck gamma e1 in
    let new_gamma = extend gamma v1 t1 in
    typecheck new_gamma e2
  | LetRec(v1, expt, e1, e2) -> 
    let new_gamma = extend gamma v1 expt in
    let t1 = typecheck new_gamma e1 in
    if is_subtype t1 expt then
      typecheck new_gamma e2
    else raise (InvalidInputException("not right"))
  | _ -> raise (TypeError("GG!"))