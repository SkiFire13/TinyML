module Tests

open Xunit
open FSharp.Common
open TinyML
open TinyML.Ast
open TinyML.Typing

let parse_expr_from_string str = Parsing.parse_from_string SyntaxError str "TEST" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId

let assert_inferred_type_eq str expected_ty =
    let tenv = List.map (fun (n, t) -> (n, Forall (Set.empty, t))) []
    let expr = parse_expr_from_string str
    let (expr_ty, _) = typeinfer_expr tenv expr
    Assert.Equal ((normalize_ty expr_ty), expected_ty)

let assert_inference_error str =
    let tenv = List.map (fun (n, t) -> (n, Forall (Set.empty, t))) []
    let expr = parse_expr_from_string str
    let failed =
        try
            let _ = typeinfer_expr tenv expr
            false
        with _ ->
            true
    if not failed then Assert.Fail "Type inference didn't fail"

[<Fact>]
let ``Test literals`` () =
    assert_inferred_type_eq "1" TyInt
    assert_inferred_type_eq "true" TyBool
    assert_inferred_type_eq "false" TyBool
    assert_inferred_type_eq "1.0" TyFloat
    assert_inferred_type_eq "\"foo\"" TyString
    assert_inferred_type_eq "'c'" TyChar
    assert_inferred_type_eq "()" TyUnit

    assert_inference_error "1 + true"
    assert_inference_error "if 1 then () else ()"
    assert_inference_error "if true then 1 else 1.0"

[<Fact>]
let ``Test let`` () =
    assert_inferred_type_eq "let a = 1 in a" TyInt
    assert_inferred_type_eq "let a = \"foo\" in a" TyString
    assert_inferred_type_eq "let f x = x in f" (TyArrow (TyVar 0, TyVar 0))
    assert_inferred_type_eq
        "let f x y = if true then x else y in let g x y z = f x (f y z) in g"
        (TyArrow (TyVar 0, TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
    assert_inferred_type_eq
        "let f x y = if true then x else y in let g x y z = f (f x 0) (f y z) in g"
        (TyArrow (TyInt, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    assert_inferred_type_eq
        "let f x y = if true then x else y in let g x y z = f (f x y) (f 0 z) in g"
        (TyArrow (TyInt, TyArrow (TyInt, TyArrow (TyInt, TyInt))))

    assert_inference_error "let x : int = 1.0 in x"
    assert_inference_error "let x : bool = 1 in x"

[<Fact>]
let ``Test let-rec`` () =
    assert_inferred_type_eq
        "let rec f x = if x < 1 then 0 else f (x - 1) in f"
        (TyArrow (TyInt, TyInt))
    assert_inferred_type_eq
        "let rec fact x = if x = 0 then 1 else x * fact (x - 1) in fact"
        (TyArrow (TyInt, TyInt))

    assert_inference_error "let rec f x = f f in f"

[<Fact>]
let ``Test lambda`` () =
    assert_inferred_type_eq "fun x -> x" (TyArrow (TyVar 0, TyVar 0))
    assert_inferred_type_eq "fun x -> x + 1" (TyArrow (TyInt, TyInt))

[<Fact>]
let ``Test app`` () =
    assert_inferred_type_eq "let f x = x in f 2" TyInt
    assert_inferred_type_eq "let f x y = x + y in f 2" (TyArrow (TyInt, TyInt))

    assert_inference_error "fun f -> f f"
    assert_inference_error "1 2"
    assert_inference_error "let f (x : int) = 1 in f 1.0"

[<Fact>]
let ``Test if-then-else`` () =
    assert_inferred_type_eq
        "fun x y z -> if x then y else z"
        (TyArrow (TyBool, TyArrow (TyVar 0, TyArrow (TyVar 0, TyVar 0))))
    assert_inferred_type_eq
        "fun x y -> if x then x else y"
        (TyArrow (TyBool, TyArrow (TyBool, TyBool)))
    assert_inferred_type_eq
        "let f x y = if x then y else y + 1 in f"
        (TyArrow (TyBool, TyArrow (TyInt, TyInt)))

    assert_inference_error "fun x -> if x then x else x + 1"

[<Fact>]
let ``Test tuple`` () =
    assert_inferred_type_eq
        "(1, 2.0, true, \"foo\", 'c', ())"
        (TyTuple [ TyInt; TyFloat; TyBool; TyString; TyChar; TyUnit ])
    assert_inferred_type_eq "let x = 1 in (x, x)" (TyTuple [ TyInt; TyInt ])
    assert_inferred_type_eq
        "let f x y z = (if true then x else y, if true then x else z) in f"
        (TyArrow (TyVar 0, TyArrow (TyVar 0, TyArrow (TyVar 0, TyTuple [ TyVar 0; TyVar 0]))))
    assert_inferred_type_eq
        "let f x y z = (if true then x else y, if true then x else z, x + 1) in f"
        (TyArrow (TyInt, TyArrow (TyInt, TyArrow (TyInt, TyTuple [ TyInt; TyInt; TyInt ]))))
    assert_inferred_type_eq
        "let f x y z = (if true then x else y, if true then x else z, z + 1) in f"
        (TyArrow (TyInt, TyArrow (TyInt, TyArrow (TyInt, TyTuple [ TyInt; TyInt; TyInt ]))))

    assert_inference_error "let x : int * int = (1, 2, 3) in x"
    assert_inference_error
        "let f x y z = (if true then x else y, if true then x else z, z + 1, not x) in f"
