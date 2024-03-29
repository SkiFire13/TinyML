﻿(*
* TinyML
* Main.fs: main code
*)

module TinyML.Main

open System
open FSharp.Common
open TinyML.Ast

let parse_from_TextReader rd filename parser = Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId
    
let interpret_expr tenv venv e =
    #if DEBUG
    printfn "AST:\t%A\npretty:\t%s" e (pretty_expr e)
    #endif
    let (t, _) = Typing.typeinfer_expr tenv e
    #if DEBUG
    printfn "type:\t%s" (pretty_ty t)
    #endif
    let v = Eval.eval_expr venv e
    #if DEBUG
    printfn "value:\t%s\n" (pretty_value v)
    #endif
    Forall (Typing.freevars_ty t, t), v

let trap f =
    try f ()
    with SyntaxError (msg, lexbuf) -> printfn "\nsyntax error: %s\nat token: %A\nlocation: %O" msg lexbuf.Lexeme lexbuf.EndPos
       | TypeError msg             -> printfn "\ntype error: %s" msg
       | LexicalError msg          -> printfn "\nlexical error: %s" msg
       | UnexpectedError msg       -> printfn "\nunexpected error: %s" msg

let main_interpreter filename =
    trap <| fun () ->
        printfn "loading source file '%s'..." filename
        use fstr = new IO.FileStream (filename, IO.FileMode.Open)
        use rd = new IO.StreamReader (fstr)
        let prg = parse_from_TextReader rd filename Parser.program 
        let Forall (_, t), v = interpret_expr [] [] prg
        printfn "type:\t%s\nvalue:\t%s" (pretty_ty t) (pretty_value v)

let main_interactive () =
    printfn "entering interactive mode..."
    let mutable tenv = []
    let mutable venv = []
    while true do
        trap <| fun () ->
            printf "\n> "
            stdout.Flush ()
            let x, (Forall (_, t), v) =
                match parse_from_TextReader stdin "LINE" Parser.interactive with 
                | IExpr e ->
                    PVariable "it", interpret_expr tenv venv e

                | IBinding (_, x, _, _ as b) ->
                    let rec pattern_to_expr p =
                        match p with
                        | PVariable x -> Var x
                        | PTuple ps -> Tuple (List.map pattern_to_expr ps)
                    let s, v = interpret_expr tenv venv (LetIn (b, pattern_to_expr x)) // TRICK: put the variable itself as body after the in
                    // update global environments
                    tenv <- Typing.bind_pat x s tenv
                    venv <- Eval.bind_pat x v venv
                    x, (s, v)

            printfn "val %s : %s = %s" (pretty_pattern x) (pretty_ty t) (pretty_value v)
                
    
[<EntryPoint>]
let main argv =
    let r =
        try 
            if argv.Length < 1 then main_interactive ()
            else main_interpreter argv.[0]
            0
        with e -> printfn "\nexception caught: %O" e; 1
    Console.ReadLine () |> ignore
    r
