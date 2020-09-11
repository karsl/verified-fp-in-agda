----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module postfix-types where

open import lib
open import parse-tree

posinfo = string
num = string
num-plus-3 = string
num-range-2 = string

mutual

  data postfix : Set where 
    Num : num → postfix
    Plus : postfix → postfix → postfix

  data start : Set where 
    Postfix : postfix → start-opt-1 → start

  data start-opt-1 : Set where 
    Postfix-0 : start-opt-1
    Postfix-1 : start-opt-1

-- embedded types:

data ParseTreeT : Set where
  parsed-postfix : postfix → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-start-opt-1 : start-opt-1 → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-num : num → ParseTreeT
  parsed-num-plus-3 : num-plus-3 → ParseTreeT
  parsed-num-range-2 : num-range-2 → ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"
numToString : num → string
numToString x = "(num " ^ x ^ ")"
num-plus-3ToString : num-plus-3 → string
num-plus-3ToString x = "(num-plus-3 " ^ x ^ ")"
num-range-2ToString : num-range-2 → string
num-range-2ToString x = "(num-range-2 " ^ x ^ ")"

mutual
  postfixToString : postfix → string
  postfixToString (Num x0) = "(Num" ^ " " ^ (numToString x0) ^ ")"
  postfixToString (Plus x0 x1) = "(Plus" ^ " " ^ (postfixToString x0) ^ " " ^ (postfixToString x1) ^ ")"

  startToString : start → string
  startToString (Postfix x0 x1) = "(Postfix" ^ " " ^ (postfixToString x0) ^ " " ^ (start-opt-1ToString x1) ^ ")"

  start-opt-1ToString : start-opt-1 → string
  start-opt-1ToString (Postfix-0) = "Postfix-0" ^ ""
  start-opt-1ToString (Postfix-1) = "Postfix-1" ^ ""

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-postfix t) = postfixToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-start-opt-1 t) = start-opt-1ToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString (parsed-num t) = numToString t
ParseTreeToString (parsed-num-plus-3 t) = num-plus-3ToString t
ParseTreeToString (parsed-num-range-2 t) = num-range-2ToString t

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-start-opt-1 : (x : start-opt-1) → start-opt-1
  norm-start-opt-1 x = x

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-postfix : (x : postfix) → postfix
  norm-postfix x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

