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
    Assert.Equal ((normalize_ty expr_ty), expected_ty)

let assert_inference_error str =
    let tenv = List.map (fun (n, t) -> (n, Forall (Set.empty, t))) gamma0
    let expr = parse_expr_from_string str
    try
        let _ = typeinfer_expr tenv expr
        Assert.Fail "Type inference didn't fail"
    with _ ->
        ()

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

[<Fact>]
let ``Test simple application`` () =
    assert_inferred_type_eq "let f x = x in f 2" TyInt
    assert_inferred_type_eq "let f x y = x + y in f 2" (TyArrow (TyInt, TyInt))

[<Fact>]
let ``Test simple let scheme`` () =
    assert_inferred_type_eq "let f x = x in f" (TyArrow (TyVar 0, TyVar 0))

[<Fact>]
let ``Test simple if-then-else`` () =
    assert_inferred_type_eq
        "fun x y z -> if x then y else z"
        (TyArrow (TyBool, TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
    assert_inferred_type_eq
        "fun x y -> if x then x else y"
        (TyArrow (TyBool, TyArrow (TyBool, TyBool)))

[<Fact>]
let ``Test simple tuple`` () =
    assert_inferred_type_eq
        "(1, 2.0, true, \"foo\", 'c', ())"
        (TyTuple [ TyInt; TyFloat; TyBool; TyString; TyChar; TyUnit ])
    assert_inferred_type_eq "let x = 1 in (x, x)" (TyTuple [ TyInt; TyInt ])

[<Fact>]
let ``Test simple let-rec`` () =
    assert_inferred_type_eq
        "let rec f x = if x < 1 then 0 else f (x - 1) in f"
        (TyArrow (TyInt, TyInt))

[<Fact>]
let ``Test weird expression`` () =
    assert_inferred_type_eq
        "fun x y f1 f2 f3 -> (f1 y, f2 y, f3 y,
            (((if true then f1 else f2) x) + ((if true then f1 else f3) x)), y + 1)"
        (
            TyArrow (TyInt, 
            TyArrow (TyInt, 
            TyArrow (TyArrow(TyInt, TyInt), 
            TyArrow (TyArrow(TyInt, TyInt), 
            TyArrow (TyArrow(TyInt, TyInt), 
            TyTuple [TyInt; TyInt; TyInt; TyInt; TyInt]
        ))))))

[<Fact>]
let ``Test let type error`` () =
    assert_inference_error "let x : int = 1.0 in x"
    assert_inference_error "let x : bool = 1 in x"

[<Fact>]
let ``Test literal type error`` () =
    assert_inference_error "1 + true"
    assert_inference_error "if 1 then () else ()"
    assert_inference_error "if true then 1 else 1.0"

[<Fact>]
let ``Test tuple types`` () =
    assert_inference_error "let x : int * int = (1, 2, 3) in x"

[<Fact>]
let ``Test recursive type`` () =
    assert_inference_error "let rec f x = f f in f"
