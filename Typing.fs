(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt
let lexical_error fmt = throw_formatted LexicalError fmt

// Type inference

let rec bind_pat p (Forall (tvs, t) as s) env =
    match p, t with
    | PVariable x, _ -> (x, s) :: env
    | PTuple ps, TyTuple ts when List.length ps = List.length ts ->
        List.foldBack2 bind_pat ps (List.map (fun t -> Forall (tvs, t)) ts) env
    | _ -> unexpected_error "the type of a tuple pattern was not a tuple with the same size"

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t) : scheme) : tyvar Set = freevars_ty t - tvs

let freevars_scheme_env (env : scheme env) : tyvar Set =
    List.fold (fun fv (_, sch) -> fv + freevars_scheme sch) Set.empty env

type subst = (tyvar * ty) list

let rec apply_subst_ty (s : subst) (t : ty) : ty =
    match t with
    | TyName _ -> t
    | TyArrow (t1, t2) -> TyArrow ((apply_subst_ty s t1), (apply_subst_ty s t2))
    | TyVar tv ->
        match List.tryFind (fun (stv, _) -> stv = tv) s with
        | Some (_, t) -> t
        | None -> t
    | TyTuple ts -> TyTuple (List.map (apply_subst_ty s) ts)

let apply_subst_scheme (s : subst) (Forall (ftv, t) : scheme) : scheme =
    Forall (ftv, apply_subst_ty s t)

let apply_subst_env (s : subst) (env : scheme env) : scheme env =
    List.map (fun (n, sch) -> (n, apply_subst_scheme s sch)) env

let compose_subst (snew : subst) (sold : subst) : subst =
    snew @ List.map (fun (tv, t) -> (tv, apply_subst_ty snew t)) sold

let compose_all_substs (ss : subst list) : subst = List.reduce compose_subst ss

let unify (fe : string -> string -> unit) (t1 : ty) (t2 : ty) : subst =
    let rec unify_inner t1 t2 : subst * bool =
        match (t1, t2) with
        | (TyName n1, TyName n2) when n1 = n2 -> [], false
        | (TyArrow (t1, t2), TyArrow (t3, t4)) ->
            let s1, e1 = unify_inner t1 t3
            if e1 then s1, e1 else
                let s2, e2 = unify_inner (apply_subst_ty s1 t2) (apply_subst_ty s1 t4)
                (compose_subst s2 s1), e2
        | (TyVar tv1, TyVar tv2) when tv1 = tv2 -> [], false
        | (TyVar tv, t) | (t, TyVar tv) when not (Set.contains tv (freevars_ty t)) -> [(tv, t)], false
        | (TyTuple ts1, TyTuple ts2) when List.length ts1 = List.length ts2 ->
            List.fold2 (fun (s, e) t1 t2 ->
                if e then s,e else
                    let su, eu = unify_inner (apply_subst_ty s t1) (apply_subst_ty s t2)
                    (compose_subst su s), eu
            ) ([], false) ts1 ts2
        | _ -> [], true
    let s, e = unify_inner t1 t2
    if e then 
        let tyvarmap, t1 = normalize_ty_with [] (apply_subst_ty s t1)
        let _, t2 = normalize_ty_with tyvarmap (apply_subst_ty s t2)
        fe (pretty_ty_raw t1) (pretty_ty_raw t2)
    s

module TyVarGenerator =
    let mutable private next_ty_var : tyvar = 0
    let fresh_ty_var () : ty =
        let ty = TyVar next_ty_var
        next_ty_var <- next_ty_var + 1;
        ty
let fresh_ty_var = TyVarGenerator.fresh_ty_var

let refresh_scheme (Forall (tvs, ty) : scheme) : ty =
    let s = List.map (fun tv -> (tv, fresh_ty_var())) (Set.toList tvs)
    apply_subst_ty s ty

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x ->
        let sch =
            match List.tryFind (fun (n, _) -> n = x) env with
            | Some (_, sch) -> sch
            | None -> lexical_error "variable %s is not defined" x
        refresh_scheme sch, []

    | Lambda (x, txo, tro, e) ->
        let tx = Option.defaultWith fresh_ty_var txo
        let (t, s) = typeinfer_expr ((x, Forall (Set.empty, tx)) :: env) e
        let fe = type_error "type annotation in let binding is wrong: expected %s, but got %s"
        let s = Option.defaultValue s (Option.map (fun tr -> compose_subst (unify fe tr t) s) tro)
        TyArrow (apply_subst_ty s tx, apply_subst_ty s t), s

    | App (e1, e2) ->
        let (t1, s1) = typeinfer_expr env e1
        let (t2, s2) = typeinfer_expr (apply_subst_env s1 env) e2
        let t3, t4 = fresh_ty_var(), fresh_ty_var()
        let fe _ = type_error "expecting a function on left side of application, but got %s"
        let s3 = unify fe (TyArrow (t3, t4)) (apply_subst_ty s2 t1)
        let fe = type_error "wrong application: argument type %s does not match function domain %s"
        let s4 = unify fe (apply_subst_ty s3 t2) (apply_subst_ty s3 t3)
        let s = compose_all_substs [ s4; s3; s2; s1]
        apply_subst_ty s t4, s

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_env s1 env
        let fe t1 tr = type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" (pretty_pattern x) tr t1
        let so = Option.defaultValue [] (Option.map (unify fe t1) tyo)
        let fe = type_error "binding %s was expecting a tuple type %s but got type %s" (pretty_pattern x)
        let rec ty_of_pat p =
            match p with
            | PVariable _ -> fresh_ty_var()
            | PTuple ps -> TyTuple (List.map ty_of_pat ps)
        let sp = compose_subst (unify fe (ty_of_pat x) (apply_subst_ty so t1)) so
        let env = apply_subst_env sp env
        let t1 = apply_subst_ty sp t1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr (bind_pat x sch env) e2
        t2, compose_all_substs [ s2; sp; s1 ]

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let fe _ = type_error "if condition must be a bool, but got a %s"
        let sb = compose_subst (unify fe TyBool t1) s1
        let env = apply_subst_env sb env
        let t2, s2 = typeinfer_expr env e2
        let env = apply_subst_env s2 env
        let t3, s3 = Option.defaultValue (TyUnit, []) (Option.map (typeinfer_expr env) e3o)
        let fe tt te =
            match e3o with
            | Some _ -> type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" tt te
            | None -> type_error "if-then without else requires unit type on then branch, but got %s" tt
        let su = unify fe (apply_subst_ty s3 t2) t3
        apply_subst_ty su t3, compose_all_substs [ su; s3; s2; sb ]

    | Tuple es ->
        let acc_ty_subst (ts, s) e =
            let t, sn = typeinfer_expr (apply_subst_env s env) e
            ts @ [t], compose_subst sn s
        let tys, s = List.fold acc_ty_subst ([], []) es
        apply_subst_ty s (TyTuple tys), s

    | LetRec (f, tfo, e1, e2) ->
        let f = match f with PVariable f -> f | _ -> unexpected_error "non-variable binding in let-rec"
        let tf = Option.defaultWith fresh_ty_var tfo
        let t1, s1 = typeinfer_expr ((f, Forall (Set.empty, tf)) :: env) e1
        let fe _ = type_error "let rec is restricted to functions, but got type %s"
        let ty_arrow = TyArrow (fresh_ty_var(), fresh_ty_var())
        let sf = compose_subst (unify fe ty_arrow (apply_subst_ty s1 t1)) s1
        let fe = type_error "let rec type mismatch: expected %s, but got %s"
        let sf = compose_subst (unify fe (apply_subst_ty sf tf) t1) sf
        let env = apply_subst_env sf env
        let t1 = apply_subst_ty sf t1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((f, sch) :: env) e2
        t2, compose_subst s2 sf

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let check_or_infer_num so e =
            let t, s = typeinfer_expr (apply_subst_env so env) e
            let fe _ = type_error "binary operator %s expects numeric operands, but got %s" op
            match t with
            | TyInt | TyFloat -> t, (compose_subst s so)
            | _ -> TyInt, compose_all_substs [ (unify fe TyInt t); s; so ]
        let t1, s1 = check_or_infer_num [] e1
        let t2, s2 = check_or_infer_num s1 e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt, s2
        | _ -> TyFloat, s2

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let fe _ = type_error "binary operator %s expects int operands, but got %s" op
        let s1b = compose_subst (unify fe TyInt t1) s1
        let t2, s2 = typeinfer_expr (apply_subst_env s1b env) e2
        TyBool, compose_all_substs [ (unify fe TyInt t2); s2; s1b ]

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let fe _ = type_error "binary operator %s expects bool operands, but got %s" op
        let s1b = compose_subst (unify fe TyBool t1) s1
        let t2, s2 = typeinfer_expr (apply_subst_env s1b env) e2
        TyBool, compose_all_substs [ (unify fe TyBool t2); s2; s1b ]

    | UnOp ("not", e) ->
        let t, s = typeinfer_expr env e
        let fe _ = type_error "unary not operator expects a bool operand, but got %s"
        TyBool, compose_subst (unify fe TyBool t) s

    | UnOp ("-", e) ->
        let t, s = typeinfer_expr env e
        let fe _ = type_error "unary negation operator expects a numeric operand, but got %s"
        match t with
        | TyInt | TyFloat -> t, s
        | _ -> TyInt, compose_subst (unify fe TyInt t) s

    | _ -> failwithf "not implemented"

// Type checker
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

    | Lambda (_x, None, _, _e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, tro, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        match tro with
        | None -> ()
        | Some tr -> if tr <> t2 then type_error "type annotation in let binding is wrong: exptected %s, but got %s" (pretty_ty tr) (pretty_ty t1)
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
        let x = match x with PVariable x -> x | _ -> unexpected_error "non-variable binding not supported"
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

    | LetRec (_f, None, _e1, _e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let f = match f with PVariable f -> f | _ -> unexpected_error "non-variable binding in let-rec"
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
