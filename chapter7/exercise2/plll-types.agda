----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module plll-types where

open import lib
open import parse-tree

posinfo = string

mutual

  data list-comma : Set where 
    List-comma : list-comma-star-3 → list-seq → list-comma-star-4 → list-comma

  data list-comma-star-3 : Set where 
    List-comma-0 : list-comma-star-3
    List-comma-1 : list-comma-star-3 → list-comma-star-3

  data list-comma-star-4 : Set where 
    List-comma-2 : list-comma-star-4
    List-comma-3 : list-comma-star-4 → list-comma-star-4

  data list-lit : Set where 
    List-lit : list-lit

  data list-seq : Set where 
    List-seq : list-seq-star-7 → list-seq-star-8 → list-lit → list-seq

  data list-seq-star-5 : Set where 
    List-seq-0 : list-seq-star-5
    List-seq-1 : list-seq-star-5 → list-seq-star-5

  data list-seq-star-6 : Set where 
    List-seq-2 : list-seq-star-6
    List-seq-3 : list-seq-star-6 → list-seq-star-6

  data list-seq-star-7 : Set where 
    List-seq-4 : list-seq-star-7
    List-seq-5 : list-seq-star-5 → list-lit → list-seq-star-6 → list-seq-star-7 → list-seq-star-7

  data list-seq-star-8 : Set where 
    List-seq-6 : list-seq-star-8
    List-seq-7 : list-seq-star-8 → list-seq-star-8

  data listt : Set where 
    Listt : listt-bar-2 → listt

  data listt-bar-2 : Set where 
    Listt-0 : list-comma → listt-bar-2
    Listt-1 : list-lit → listt-bar-2

  data start : Set where 
    Start : listt → start-opt-1 → start

  data start-opt-1 : Set where 
    Start-0 : start-opt-1
    Start-1 : start-opt-1

-- embedded types:

data ParseTreeT : Set where
  parsed-list-comma : list-comma → ParseTreeT
  parsed-list-comma-star-3 : list-comma-star-3 → ParseTreeT
  parsed-list-comma-star-4 : list-comma-star-4 → ParseTreeT
  parsed-list-lit : list-lit → ParseTreeT
  parsed-list-seq : list-seq → ParseTreeT
  parsed-list-seq-star-5 : list-seq-star-5 → ParseTreeT
  parsed-list-seq-star-6 : list-seq-star-6 → ParseTreeT
  parsed-list-seq-star-7 : list-seq-star-7 → ParseTreeT
  parsed-list-seq-star-8 : list-seq-star-8 → ParseTreeT
  parsed-listt : listt → ParseTreeT
  parsed-listt-bar-2 : listt-bar-2 → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-start-opt-1 : start-opt-1 → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"

mutual
  list-commaToString : list-comma → string
  list-commaToString (List-comma x0 x1 x2) = "(List-comma" ^ " " ^ (list-comma-star-3ToString x0) ^ " " ^ (list-seqToString x1) ^ " " ^ (list-comma-star-4ToString x2) ^ ")"

  list-comma-star-3ToString : list-comma-star-3 → string
  list-comma-star-3ToString (List-comma-0) = "List-comma-0" ^ ""
  list-comma-star-3ToString (List-comma-1 x0) = "(List-comma-1" ^ " " ^ (list-comma-star-3ToString x0) ^ ")"

  list-comma-star-4ToString : list-comma-star-4 → string
  list-comma-star-4ToString (List-comma-2) = "List-comma-2" ^ ""
  list-comma-star-4ToString (List-comma-3 x0) = "(List-comma-3" ^ " " ^ (list-comma-star-4ToString x0) ^ ")"

  list-litToString : list-lit → string
  list-litToString (List-lit) = "List-lit" ^ ""

  list-seqToString : list-seq → string
  list-seqToString (List-seq x0 x1 x2) = "(List-seq" ^ " " ^ (list-seq-star-7ToString x0) ^ " " ^ (list-seq-star-8ToString x1) ^ " " ^ (list-litToString x2) ^ ")"

  list-seq-star-5ToString : list-seq-star-5 → string
  list-seq-star-5ToString (List-seq-0) = "List-seq-0" ^ ""
  list-seq-star-5ToString (List-seq-1 x0) = "(List-seq-1" ^ " " ^ (list-seq-star-5ToString x0) ^ ")"

  list-seq-star-6ToString : list-seq-star-6 → string
  list-seq-star-6ToString (List-seq-2) = "List-seq-2" ^ ""
  list-seq-star-6ToString (List-seq-3 x0) = "(List-seq-3" ^ " " ^ (list-seq-star-6ToString x0) ^ ")"

  list-seq-star-7ToString : list-seq-star-7 → string
  list-seq-star-7ToString (List-seq-4) = "List-seq-4" ^ ""
  list-seq-star-7ToString (List-seq-5 x0 x1 x2 x3) = "(List-seq-5" ^ " " ^ (list-seq-star-5ToString x0) ^ " " ^ (list-litToString x1) ^ " " ^ (list-seq-star-6ToString x2) ^ " " ^ (list-seq-star-7ToString x3) ^ ")"

  list-seq-star-8ToString : list-seq-star-8 → string
  list-seq-star-8ToString (List-seq-6) = "List-seq-6" ^ ""
  list-seq-star-8ToString (List-seq-7 x0) = "(List-seq-7" ^ " " ^ (list-seq-star-8ToString x0) ^ ")"

  listtToString : listt → string
  listtToString (Listt x0) = "(Listt" ^ " " ^ (listt-bar-2ToString x0) ^ ")"

  listt-bar-2ToString : listt-bar-2 → string
  listt-bar-2ToString (Listt-0 x0) = "(Listt-0" ^ " " ^ (list-commaToString x0) ^ ")"
  listt-bar-2ToString (Listt-1 x0) = "(Listt-1" ^ " " ^ (list-litToString x0) ^ ")"

  startToString : start → string
  startToString (Start x0 x1) = "(Start" ^ " " ^ (listtToString x0) ^ " " ^ (start-opt-1ToString x1) ^ ")"

  start-opt-1ToString : start-opt-1 → string
  start-opt-1ToString (Start-0) = "Start-0" ^ ""
  start-opt-1ToString (Start-1) = "Start-1" ^ ""

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-list-comma t) = list-commaToString t
ParseTreeToString (parsed-list-comma-star-3 t) = list-comma-star-3ToString t
ParseTreeToString (parsed-list-comma-star-4 t) = list-comma-star-4ToString t
ParseTreeToString (parsed-list-lit t) = list-litToString t
ParseTreeToString (parsed-list-seq t) = list-seqToString t
ParseTreeToString (parsed-list-seq-star-5 t) = list-seq-star-5ToString t
ParseTreeToString (parsed-list-seq-star-6 t) = list-seq-star-6ToString t
ParseTreeToString (parsed-list-seq-star-7 t) = list-seq-star-7ToString t
ParseTreeToString (parsed-list-seq-star-8 t) = list-seq-star-8ToString t
ParseTreeToString (parsed-listt t) = listtToString t
ParseTreeToString (parsed-listt-bar-2 t) = listt-bar-2ToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-start-opt-1 t) = start-opt-1ToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t

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
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-listt-bar-2 : (x : listt-bar-2) → listt-bar-2
  norm-listt-bar-2 x = x

  {-# TERMINATING #-}
  norm-listt : (x : listt) → listt
  norm-listt x = x

  {-# TERMINATING #-}
  norm-list-seq-star-8 : (x : list-seq-star-8) → list-seq-star-8
  norm-list-seq-star-8 x = x

  {-# TERMINATING #-}
  norm-list-seq-star-7 : (x : list-seq-star-7) → list-seq-star-7
  norm-list-seq-star-7 x = x

  {-# TERMINATING #-}
  norm-list-seq-star-6 : (x : list-seq-star-6) → list-seq-star-6
  norm-list-seq-star-6 x = x

  {-# TERMINATING #-}
  norm-list-seq-star-5 : (x : list-seq-star-5) → list-seq-star-5
  norm-list-seq-star-5 x = x

  {-# TERMINATING #-}
  norm-list-seq : (x : list-seq) → list-seq
  norm-list-seq x = x

  {-# TERMINATING #-}
  norm-list-lit : (x : list-lit) → list-lit
  norm-list-lit x = x

  {-# TERMINATING #-}
  norm-list-comma-star-4 : (x : list-comma-star-4) → list-comma-star-4
  norm-list-comma-star-4 x = x

  {-# TERMINATING #-}
  norm-list-comma-star-3 : (x : list-comma-star-3) → list-comma-star-3
  norm-list-comma-star-3 x = x

  {-# TERMINATING #-}
  norm-list-comma : (x : list-comma) → list-comma
  norm-list-comma x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

