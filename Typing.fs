(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

type subst = (tyvar * ty) list

let rec apply_subst_ty (s : subst) (t : ty) : ty =
    match t with
    | TyName n -> t
    | TyArrow (t1, t2) -> TyArrow ((apply_subst_ty s t1), (apply_subst_ty s t2))
    | TyVar tv -> match List.tryFind (fun (stv, _) -> stv = tv) s with
        | Some (_, t) -> t
        | None -> t
    | TyTuple ts -> TyTuple (List.map (apply_subst_ty s) ts)

let apply_subst_scheme (s : subst) (Forall (ftv, t) : scheme) : scheme =
    Forall (ftv, apply_subst_ty s t)

let apply_subst_env (s : subst) (env : scheme env) : scheme env =
    List.map (fun (n, sch) -> (n, apply_subst_scheme s sch)) env

let compose_subst (s1 : subst) (s2 : subst) : subst =
    s1 @ List.map (fun (tv, t) -> (tv, apply_subst_ty s1 t)) s2

let rec unify (t1 : ty) (t2 : ty) : subst =
    match (t1, t2) with
    | (TyName n1, TyName n2) when n1 = n2 -> []
    | (TyArrow (t1, t2), TyArrow (t3, t4)) ->
        let s1 = unify t1 t3
        let s2 = unify (apply_subst_ty s1 t2) (apply_subst_ty s1 t4)
        compose_subst s2 s1
    | (TyVar tv1, TyVar tv2) when tv1 = tv2 -> []
    | (TyVar tv, t) | (t, TyVar tv) when not (Set.contains tv (freevars_ty t)) -> [(tv, t)]
    | (TyTuple ts1, TyTuple ts2) when List.length ts1 = List.length ts2 ->
        let compose_unify s t1 t2 = compose_subst (unify (apply_subst_ty s t1) (apply_subst_ty s t2)) s
        List.fold2 compose_unify [] ts1 ts2
    | _ -> type_error "unification error: expected %s got %s" (pretty_ty t1) (pretty_ty t2)

module TyVarGenerator =
    let mutable private next_ty_var: tyvar = 0
    let fresh_ty_var (): ty =
        let ty = TyVar next_ty_var
        next_ty_var <- next_ty_var + 1;
        ty
let fresh_ty_var = TyVarGenerator.fresh_ty_var

let refresh_scheme (Forall (tvs, ty) : scheme) : ty =
    let s = List.map (fun tv -> (tv, fresh_ty_var())) (Set.toList tvs)
    apply_subst_ty s ty

// type inference
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))

]



// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x ->
        let _, sch = List.find (fun (n, _) -> n = x) env
        refresh_scheme sch, []

    | Lambda (x, txo, e) ->
        let tx = Option.defaultWith fresh_ty_var txo
        let (t, s) = typeinfer_expr ((x, Forall (Set.empty, tx)) :: env) e
        TyArrow (apply_subst_ty s tx, t), s

        
    | App (e1, e2) ->
        let (t1, s1) = typeinfer_expr env e1
        let (t2, s2) = typeinfer_expr (apply_subst_env s1 env) e2
        let t3 = fresh_ty_var()
        let s3 = unify (apply_subst_ty s2 t1) (TyArrow (t2, t3))
        apply_subst_ty s3 t3, compose_subst (compose_subst s3 s2) s1

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_env s1 env
        let so = Option.defaultValue [] (Option.map (unify t1) tyo)
        let env = apply_subst_env so env
        let t1 = apply_subst_ty so t1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst (compose_subst s2 so) s1

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let sb = compose_subst (unify t1 TyBool) s1
        let env = apply_subst_env sb env
        let t2, s2 = typeinfer_expr env e2
        let env = apply_subst_env s2 env
        let t3, s3 = Option.defaultValue (TyUnit, []) (Option.map (typeinfer_expr env) e3o)
        let su = unify (apply_subst_ty s3 t2) t3
        apply_subst_ty su t3, compose_subst (compose_subst su s3) (compose_subst s2 sb)
        
    | Tuple es ->
        let acc_ty_subst (ts, s) e =
            let t, sn = typeinfer_expr (apply_subst_env s env) e
            ts @ [t], compose_subst sn s
        let tys, s = List.fold acc_ty_subst ([], []) es
        apply_subst_ty s (TyTuple tys), s

    | LetRec (f, tfo, e1, e2) ->
        let tf = Option.defaultWith fresh_ty_var tfo
        let t1, s1 = typeinfer_expr ((f, Forall (Set.empty, tf)) :: env) e1
        let sf = compose_subst (unify (apply_subst_ty s1 tf) t1) s1
        let ty_arrow = TyArrow (fresh_ty_var(), fresh_ty_var())
        let sf = compose_subst (unify (apply_subst_ty sf t1) ty_arrow) sf
        let env = apply_subst_env sf env
        let t1 = apply_subst_ty sf t1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((f, sch) :: env) e2
        t2, compose_subst s2 sf

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let check_or_infer_num so e =
            let t, s = typeinfer_expr (apply_subst_env so env) e
            match t with
            | TyInt | TyFloat -> t, (compose_subst s so)
            | _ -> TyInt, compose_subst (unify t TyInt) (compose_subst s so)
        let t1, s1 = check_or_infer_num [] e1
        let t2, s2 = check_or_infer_num s1 e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt, s2
        | _ -> TyFloat, s2
    
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s1 = compose_subst (unify t1 TyInt) s1
        let t2, s2 = typeinfer_expr (apply_subst_env s1 env) e2
        let s2 = compose_subst (unify t2 TyInt) s2
        TyBool, compose_subst s2 s1

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let s1 = compose_subst (unify t1 TyBool) s1
        let t2, s2 = typeinfer_expr (apply_subst_env s1 env) e2
        let s2 = compose_subst (unify t2 TyBool) s2
        TyBool, compose_subst s2 s1

    | UnOp ("not", e) ->
        let t, s = typeinfer_expr env e
        let s = compose_subst (unify t TyBool) s
        TyBool, s

    | UnOp ("-", e) ->
        let t, s = typeinfer_expr env e
        match t with
        | TyInt | TyFloat -> t, s
        | _ -> TyInt, compose_subst (unify t TyInt) s

    | _ -> failwithf "not implemented"

// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
