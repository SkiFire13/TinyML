﻿(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

let rec bind_pat p v env =
    match p, v with
    | PVariable x, v -> (x, v) :: env
    | PTuple ps, VTuple vs -> List.foldBack2 bind_pat ps vs env
    | _ -> unexpected_error "eval_expr: tried to pattern match a tuple %s to a non-tuple value %s" (pretty_pattern p) (pretty_value v)

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda (x, _, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)

    | BinOp (e1, "|>", e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v2 with
        | Closure (env1, x, e) -> eval_expr ((x, v1) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v1) :: (f, v2) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in right side of pipe operator: %s" (pretty_value v2)
        
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )
    | Tuple es ->
        VTuple (List.map (eval_expr env) es)

    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr (bind_pat x v1 env) e2

    | LetRec (f, _, e1, e2) -> 
        let f = match f with PVariable f -> f | _ -> unexpected_error "eval_expr: expected let-rec to have a binding pattern but got: %s" (pretty_pattern f)
        let v1 = eval_expr env e1
        let v1 =
            match v1 with
            | Closure (venv1, x, e) -> RecClosure (venv1, f, x, e)
            | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        eval_expr ((f, v1) :: env) e2

    | BinOp (e1, "+", e2) -> binop (+) (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop (-) (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop ( * ) ( * ) env e1 e2
    | BinOp (e1, "/", e2) -> binop (/) (/) env e1 e2
    | BinOp (e1, "%", e2) -> binop (%) (%) env e1 e2

    | BinOp (e1, "<", e2) -> binop_comp (<) env e1 e2
    | BinOp (e1, "<=", e2) -> binop_comp (<=) env e1 e2
    | BinOp (e1, ">", e2) -> binop_comp (>) env e1 e2
    | BinOp (e1, ">=", e2) -> binop_comp (>=) env e1 e2
    | BinOp (e1, "=", e2) -> binop_comp (=) env e1 e2
    | BinOp (e1, "<>", e2) -> binop_comp (<>) env e1 e2

    | BinOp (e1, "and", e2) -> binop_bool (&&) env e1 e2
    | BinOp (e1, "or", e2) -> binop_bool (||) env e1 e2

    | UnOp ("not", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LBool x) -> VLit (LBool (not x))
        | _ -> unexpected_error "eval_expr: illegal operand in unary operator: %s" (pretty_value v)

    | UnOp ("-", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LInt x) -> VLit (LInt (-x))
        | VLit (LFloat x) -> VLit (LFloat (-x))
        | _ -> unexpected_error "eval_expr: illegal operand in unary operator: %s" (pretty_value v)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and binop op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)

and binop_comp op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)

and binop_bool op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LBool x), VLit (LBool y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s + %s" (pretty_value v1) (pretty_value v2)
