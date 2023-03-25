open Fmt
open Sedlexing
open Parser0
open Tokenize
module I = MenhirInterpreter
module S = MenhirLib.General

exception
  ParseError of
    { state : int
    ; pos_start : Lexing.position
    ; pos_end : Lexing.position
    }

let handle_error checkpoint =
  match Lazy.force (I.stack checkpoint) with
  | S.Nil -> assert false
  | S.Cons (Element (s, _, pos_start, pos_end), _) ->
    raise (ParseError { state = I.number s; pos_start; pos_end })

let rec loop next_token checkpoint =
  match checkpoint with
  | I.InputNeeded env ->
    let token = next_token () in
    loop next_token (I.offer checkpoint token)
  | I.Shifting _
  | I.AboutToReduce _ ->
    loop next_token (I.resume checkpoint)
  | I.HandlingError env -> handle_error env
  | I.Accepted tm -> tm
  | I.Rejected -> assert false

let parse lexbuf =
  let lexer = with_tokenizer tokenize lexbuf in
  loop lexer (Incremental.main (fst (lexing_positions lexbuf)))
