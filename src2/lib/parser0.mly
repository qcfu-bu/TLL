%token EOF
%token<string> IDENTIFIER

%{ open Syntax0 %}

%start <tm> main

%%

let identifier :=
  | s = IDENTIFIER; <>

let id :=
  | s = identifier; { Id s }

let main :=
  | ~ = id; EOF; <>
