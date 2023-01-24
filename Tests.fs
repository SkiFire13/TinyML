module Tests

open Xunit
open FSharp.Common
open TinyML
open TinyML.Ast
open TinyML.Typing

let parse_expr_from_string str = Parsing.parse_from_string SyntaxError str "TEST" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId

let assert_inferred_type_eq str expected_ty =
    let tenv = List.map (fun (n, t) -> (n, Forall (Set.empty, t))) gamma0
    let expr = parse_expr_from_string str
    let (expr_ty, _) = typeinfer_expr tenv expr
    let normalize_ty t =
        let rec normalize_ty_inner s t =
            match t with
            | TyName _ -> s, t
            | TyArrow (t1, t2) ->
                let s1, t1 = normalize_ty_inner s t1
                let s2, t2 = normalize_ty_inner s1 t2
                s2, TyArrow (t1, t2)
            | TyVar tv ->
                match List.tryFind (fun (tvk, _) -> tvk = tv) s with
                | Some (_, tvs) -> s, TyVar tvs
                | None -> (tv, List.length s) :: s, TyVar (List.length s)
            | TyTuple ts ->
                let s, ts = List.fold (fun (s, ts) t -> let s, t = normalize_ty_inner s t in (s, ts @ [t])) (s, []) ts
                s, TyTuple ts
        let _, t = normalize_ty_inner [] t
        t
    Assert.Equal ((normalize_ty expr_ty), (normalize_ty expected_ty))

[<Fact>]
let ``Test literals`` () =
    assert_inferred_type_eq "1" TyInt
    assert_inferred_type_eq "true" TyBool
    assert_inferred_type_eq "false" TyBool
    assert_inferred_type_eq "1.0" TyFloat
    assert_inferred_type_eq "\"foo\"" TyString
    assert_inferred_type_eq "'c'" TyChar
    assert_inferred_type_eq "()" TyUnit

[<Fact>]
let ``Test simple let`` () =
    assert_inferred_type_eq "let a = 1 in a" TyInt
    assert_inferred_type_eq "let a = \"foo\" in a" TyString

[<Fact>]
let ``Test simple lambda`` () =
    assert_inferred_type_eq "fun x -> x" (TyArrow (TyVar 0, TyVar 0))
    assert_inferred_type_eq "fun x -> x + 1" (TyArrow (TyInt, TyInt))
