import Autosubst
open Autosubst Autosubst.Notation

namespace SysfSN

inductive Srt where
  | U
  | L

inductive Rlv where
  | im
  | ex

autosubst
  Chan where

  Term where
    -- core
    | srt  : Srt → Term
    | pi   : Term → (bind Term in Term) → Rlv → Srt → Term
    | lam  : Term → (bind Term in Term) → Rlv → Srt → Term
    | app  : Term → Term → Rlv → Term
    | sig  : Term → (bind Term in Term) → Rlv → Srt → Term
    | pair : Term → Term → Rlv → Srt → Term
    | proj : Term → Term → (bind Term, Term in Term) → Term
    | fix  : Term → (bind Term in Term) → Term
    -- data
    | unit : Term
    | one  : Term
    | bool : Term
    | tt   : Term
    | ff   : Term
    | ite  : (bind Term in Term) → Term → Term → Term → Term
    -- monadic
    | M    : Term → Term
    | pure : Term → Term
    | mlet : Term → (bind Term in Term) → Term
    -- session
    | proto : Term
    | act   : Bool → Term → (bind Term in Term) → Rlv → Term
    | ch    : Bool → Term → Term
    | chan  : Chan → Term
    | fork  : Term → (bind Term in Term) → Term
    | recv  : Term → Rlv → Term
    | send  : Term → Rlv → Term
    | close : Bool → Term → Term

  Proc where
    | tm  : Term → Proc
    | par : Proc → Proc → Proc
    | res : (bind Chan in Proc) → Proc
