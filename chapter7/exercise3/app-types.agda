----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module app-types where

open import lib
open import parse-tree

posinfo = string
var = string
var-plus-2 = string
var-range-1 = string

mutual

  data expr : Set where 
    App : expr → expr → expr
    Parens : expr → expr
    Var : var → expr

  data start : Set where 
    Term : expr → start

-- embedded types:

data ParseTreeT : Set where
  parsed-expr : expr → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-var : var → ParseTreeT
  parsed-var-plus-2 : var-plus-2 → ParseTreeT
  parsed-var-range-1 : var-range-1 → ParseTreeT
  parsed-cp : ParseTreeT
  parsed-op : ParseTreeT
  parsed-owss : ParseTreeT
  parsed-owss-opt-6 : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-bar-3 : ParseTreeT
  parsed-ws-bar-4 : ParseTreeT
  parsed-wss : ParseTreeT
  parsed-wss-star-5 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"
varToString : var → string
varToString x = "(var " ^ x ^ ")"
var-plus-2ToString : var-plus-2 → string
var-plus-2ToString x = "(var-plus-2 " ^ x ^ ")"
var-range-1ToString : var-range-1 → string
var-range-1ToString x = "(var-range-1 " ^ x ^ ")"

mutual
  exprToString : expr → string
  exprToString (App x0 x1) = "(App" ^ " " ^ (exprToString x0) ^ " " ^ (exprToString x1) ^ ")"
  exprToString (Parens x0) = "(Parens" ^ " " ^ (exprToString x0) ^ ")"
  exprToString (Var x0) = "(Var" ^ " " ^ (varToString x0) ^ ")"

  startToString : start → string
  startToString (Term x0) = "(Term" ^ " " ^ (exprToString x0) ^ ")"

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-expr t) = exprToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString (parsed-var t) = varToString t
ParseTreeToString (parsed-var-plus-2 t) = var-plus-2ToString t
ParseTreeToString (parsed-var-range-1 t) = var-range-1ToString t
ParseTreeToString parsed-cp = "[cp]"
ParseTreeToString parsed-op = "[op]"
ParseTreeToString parsed-owss = "[owss]"
ParseTreeToString parsed-owss-opt-6 = "[owss-opt-6]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-bar-3 = "[ws-bar-3]"
ParseTreeToString parsed-ws-bar-4 = "[ws-bar-4]"
ParseTreeToString parsed-wss = "[wss]"
ParseTreeToString parsed-wss-star-5 = "[wss-star-5]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-expr : (x : expr) → expr
  norm-expr (App x1 (App x2 x3)) = (norm-expr (App  (norm-expr (App  x1 x2) ) x3) )
  norm-expr x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

