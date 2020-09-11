----------------------------------------------------------------------------------
-- Types for parse trees
----------------------------------------------------------------------------------

module para-types where

open import lib
open import parse-tree

posinfo = string

mutual

  data cword : Set where 
    CWord : word → cword

  data paragraph : Set where 
    Paragraph : sentence → paragraph-star-6 → paragraph

  data paragraph-bar-4 : Set where 
    Paragraph-0 : paragraph-bar-4
    Paragraph-1 : paragraph-bar-4

  data paragraph-bar-5 : Set where 
    Paragraph-2 : paragraph-bar-5
    Paragraph-3 : paragraph-bar-4 → paragraph-bar-5

  data paragraph-star-6 : Set where 
    Paragraph-4 : paragraph-star-6
    Paragraph-5 : paragraph-bar-5 → sentence → paragraph-star-6 → paragraph-star-6

  data sentence : Set where 
    Sentence : cword → sentence-star-11 → sentence-bar-12 → sentence

  data sentence-bar-10 : Set where 
    Sentence-6 : sentence-bar-10
    Sentence-7 : sentence-bar-10

  data sentence-bar-12 : Set where 
    Sentence-10 : sentence-bar-12
    Sentence-11 : sentence-bar-12

  data sentence-bar-7 : Set where 
    Sentence-0 : sentence-bar-7
    Sentence-1 : sentence-bar-7

  data sentence-bar-8 : Set where 
    Sentence-2 : sentence-bar-8
    Sentence-3 : sentence-bar-7 → sentence-bar-8

  data sentence-opt-9 : Set where 
    Sentence-4 : sentence-bar-8 → sentence-opt-9
    Sentence-5 : sentence-opt-9

  data sentence-star-11 : Set where 
    Sentence-8 : sentence-star-11
    Sentence-9 : sentence-opt-9 → sentence-bar-10 → word → sentence-star-11 → sentence-star-11

  data start : Set where 
    Start : text → start-opt-1 → start

  data start-opt-1 : Set where 
    Start-0 : start-opt-1
    Start-1 : start-opt-1

  data text : Set where 
    Text : paragraph → text-star-3 → text

  data text-bar-2 : Set where 
    Text-0 : text-bar-2
    Text-1 : text-bar-2

  data text-star-3 : Set where 
    Text-2 : text-star-3
    Text-3 : text-bar-2 → paragraph → text-star-3 → text-star-3

  data word : Set where 
    Word : word-plus-13 → word

  data word-plus-13 : Set where 
    Word-0 : word-plus-13
    Word-1 : word-plus-13 → word-plus-13

-- embedded types:

data ParseTreeT : Set where
  parsed-cword : cword → ParseTreeT
  parsed-paragraph : paragraph → ParseTreeT
  parsed-paragraph-bar-4 : paragraph-bar-4 → ParseTreeT
  parsed-paragraph-bar-5 : paragraph-bar-5 → ParseTreeT
  parsed-paragraph-star-6 : paragraph-star-6 → ParseTreeT
  parsed-sentence : sentence → ParseTreeT
  parsed-sentence-bar-10 : sentence-bar-10 → ParseTreeT
  parsed-sentence-bar-12 : sentence-bar-12 → ParseTreeT
  parsed-sentence-bar-7 : sentence-bar-7 → ParseTreeT
  parsed-sentence-bar-8 : sentence-bar-8 → ParseTreeT
  parsed-sentence-opt-9 : sentence-opt-9 → ParseTreeT
  parsed-sentence-star-11 : sentence-star-11 → ParseTreeT
  parsed-start : start → ParseTreeT
  parsed-start-opt-1 : start-opt-1 → ParseTreeT
  parsed-text : text → ParseTreeT
  parsed-text-bar-2 : text-bar-2 → ParseTreeT
  parsed-text-star-3 : text-star-3 → ParseTreeT
  parsed-word : word → ParseTreeT
  parsed-word-plus-13 : word-plus-13 → ParseTreeT
  parsed-posinfo : posinfo → ParseTreeT
  parsed-cletter : ParseTreeT
  parsed-cletter-range-14 : ParseTreeT
  parsed-colon : ParseTreeT
  parsed-comma : ParseTreeT
  parsed-dot : ParseTreeT
  parsed-letter : ParseTreeT
  parsed-letter-range-15 : ParseTreeT
  parsed-nl : ParseTreeT
  parsed-owss : ParseTreeT
  parsed-owss-opt-19 : ParseTreeT
  parsed-qmark : ParseTreeT
  parsed-semicolon : ParseTreeT
  parsed-ws : ParseTreeT
  parsed-ws-bar-16 : ParseTreeT
  parsed-ws-bar-17 : ParseTreeT
  parsed-wss : ParseTreeT
  parsed-wss-star-18 : ParseTreeT

------------------------------------------
-- Parse tree printing functions
------------------------------------------

posinfoToString : posinfo → string
posinfoToString x = "(posinfo " ^ x ^ ")"

mutual
  cwordToString : cword → string
  cwordToString (CWord x0) = "(CWord" ^ " " ^ (wordToString x0) ^ ")"

  paragraphToString : paragraph → string
  paragraphToString (Paragraph x0 x1) = "(Paragraph" ^ " " ^ (sentenceToString x0) ^ " " ^ (paragraph-star-6ToString x1) ^ ")"

  paragraph-bar-4ToString : paragraph-bar-4 → string
  paragraph-bar-4ToString (Paragraph-0) = "Paragraph-0" ^ ""
  paragraph-bar-4ToString (Paragraph-1) = "Paragraph-1" ^ ""

  paragraph-bar-5ToString : paragraph-bar-5 → string
  paragraph-bar-5ToString (Paragraph-2) = "Paragraph-2" ^ ""
  paragraph-bar-5ToString (Paragraph-3 x0) = "(Paragraph-3" ^ " " ^ (paragraph-bar-4ToString x0) ^ ")"

  paragraph-star-6ToString : paragraph-star-6 → string
  paragraph-star-6ToString (Paragraph-4) = "Paragraph-4" ^ ""
  paragraph-star-6ToString (Paragraph-5 x0 x1 x2) = "(Paragraph-5" ^ " " ^ (paragraph-bar-5ToString x0) ^ " " ^ (sentenceToString x1) ^ " " ^ (paragraph-star-6ToString x2) ^ ")"

  sentenceToString : sentence → string
  sentenceToString (Sentence x0 x1 x2) = "(Sentence" ^ " " ^ (cwordToString x0) ^ " " ^ (sentence-star-11ToString x1) ^ " " ^ (sentence-bar-12ToString x2) ^ ")"

  sentence-bar-10ToString : sentence-bar-10 → string
  sentence-bar-10ToString (Sentence-6) = "Sentence-6" ^ ""
  sentence-bar-10ToString (Sentence-7) = "Sentence-7" ^ ""

  sentence-bar-12ToString : sentence-bar-12 → string
  sentence-bar-12ToString (Sentence-10) = "Sentence-10" ^ ""
  sentence-bar-12ToString (Sentence-11) = "Sentence-11" ^ ""

  sentence-bar-7ToString : sentence-bar-7 → string
  sentence-bar-7ToString (Sentence-0) = "Sentence-0" ^ ""
  sentence-bar-7ToString (Sentence-1) = "Sentence-1" ^ ""

  sentence-bar-8ToString : sentence-bar-8 → string
  sentence-bar-8ToString (Sentence-2) = "Sentence-2" ^ ""
  sentence-bar-8ToString (Sentence-3 x0) = "(Sentence-3" ^ " " ^ (sentence-bar-7ToString x0) ^ ")"

  sentence-opt-9ToString : sentence-opt-9 → string
  sentence-opt-9ToString (Sentence-4 x0) = "(Sentence-4" ^ " " ^ (sentence-bar-8ToString x0) ^ ")"
  sentence-opt-9ToString (Sentence-5) = "Sentence-5" ^ ""

  sentence-star-11ToString : sentence-star-11 → string
  sentence-star-11ToString (Sentence-8) = "Sentence-8" ^ ""
  sentence-star-11ToString (Sentence-9 x0 x1 x2 x3) = "(Sentence-9" ^ " " ^ (sentence-opt-9ToString x0) ^ " " ^ (sentence-bar-10ToString x1) ^ " " ^ (wordToString x2) ^ " " ^ (sentence-star-11ToString x3) ^ ")"

  startToString : start → string
  startToString (Start x0 x1) = "(Start" ^ " " ^ (textToString x0) ^ " " ^ (start-opt-1ToString x1) ^ ")"

  start-opt-1ToString : start-opt-1 → string
  start-opt-1ToString (Start-0) = "Start-0" ^ ""
  start-opt-1ToString (Start-1) = "Start-1" ^ ""

  textToString : text → string
  textToString (Text x0 x1) = "(Text" ^ " " ^ (paragraphToString x0) ^ " " ^ (text-star-3ToString x1) ^ ")"

  text-bar-2ToString : text-bar-2 → string
  text-bar-2ToString (Text-0) = "Text-0" ^ ""
  text-bar-2ToString (Text-1) = "Text-1" ^ ""

  text-star-3ToString : text-star-3 → string
  text-star-3ToString (Text-2) = "Text-2" ^ ""
  text-star-3ToString (Text-3 x0 x1 x2) = "(Text-3" ^ " " ^ (text-bar-2ToString x0) ^ " " ^ (paragraphToString x1) ^ " " ^ (text-star-3ToString x2) ^ ")"

  wordToString : word → string
  wordToString (Word x0) = "(Word" ^ " " ^ (word-plus-13ToString x0) ^ ")"

  word-plus-13ToString : word-plus-13 → string
  word-plus-13ToString (Word-0) = "Word-0" ^ ""
  word-plus-13ToString (Word-1 x0) = "(Word-1" ^ " " ^ (word-plus-13ToString x0) ^ ")"

ParseTreeToString : ParseTreeT → string
ParseTreeToString (parsed-cword t) = cwordToString t
ParseTreeToString (parsed-paragraph t) = paragraphToString t
ParseTreeToString (parsed-paragraph-bar-4 t) = paragraph-bar-4ToString t
ParseTreeToString (parsed-paragraph-bar-5 t) = paragraph-bar-5ToString t
ParseTreeToString (parsed-paragraph-star-6 t) = paragraph-star-6ToString t
ParseTreeToString (parsed-sentence t) = sentenceToString t
ParseTreeToString (parsed-sentence-bar-10 t) = sentence-bar-10ToString t
ParseTreeToString (parsed-sentence-bar-12 t) = sentence-bar-12ToString t
ParseTreeToString (parsed-sentence-bar-7 t) = sentence-bar-7ToString t
ParseTreeToString (parsed-sentence-bar-8 t) = sentence-bar-8ToString t
ParseTreeToString (parsed-sentence-opt-9 t) = sentence-opt-9ToString t
ParseTreeToString (parsed-sentence-star-11 t) = sentence-star-11ToString t
ParseTreeToString (parsed-start t) = startToString t
ParseTreeToString (parsed-start-opt-1 t) = start-opt-1ToString t
ParseTreeToString (parsed-text t) = textToString t
ParseTreeToString (parsed-text-bar-2 t) = text-bar-2ToString t
ParseTreeToString (parsed-text-star-3 t) = text-star-3ToString t
ParseTreeToString (parsed-word t) = wordToString t
ParseTreeToString (parsed-word-plus-13 t) = word-plus-13ToString t
ParseTreeToString (parsed-posinfo t) = posinfoToString t
ParseTreeToString parsed-cletter = "[cletter]"
ParseTreeToString parsed-cletter-range-14 = "[cletter-range-14]"
ParseTreeToString parsed-colon = "[colon]"
ParseTreeToString parsed-comma = "[comma]"
ParseTreeToString parsed-dot = "[dot]"
ParseTreeToString parsed-letter = "[letter]"
ParseTreeToString parsed-letter-range-15 = "[letter-range-15]"
ParseTreeToString parsed-nl = "[nl]"
ParseTreeToString parsed-owss = "[owss]"
ParseTreeToString parsed-owss-opt-19 = "[owss-opt-19]"
ParseTreeToString parsed-qmark = "[qmark]"
ParseTreeToString parsed-semicolon = "[semicolon]"
ParseTreeToString parsed-ws = "[ws]"
ParseTreeToString parsed-ws-bar-16 = "[ws-bar-16]"
ParseTreeToString parsed-ws-bar-17 = "[ws-bar-17]"
ParseTreeToString parsed-wss = "[wss]"
ParseTreeToString parsed-wss-star-18 = "[wss-star-18]"

------------------------------------------
-- Reorganizing rules
------------------------------------------

mutual

  {-# TERMINATING #-}
  norm-word-plus-13 : (x : word-plus-13) → word-plus-13
  norm-word-plus-13 x = x

  {-# TERMINATING #-}
  norm-word : (x : word) → word
  norm-word x = x

  {-# TERMINATING #-}
  norm-text-star-3 : (x : text-star-3) → text-star-3
  norm-text-star-3 x = x

  {-# TERMINATING #-}
  norm-text-bar-2 : (x : text-bar-2) → text-bar-2
  norm-text-bar-2 x = x

  {-# TERMINATING #-}
  norm-text : (x : text) → text
  norm-text x = x

  {-# TERMINATING #-}
  norm-start-opt-1 : (x : start-opt-1) → start-opt-1
  norm-start-opt-1 x = x

  {-# TERMINATING #-}
  norm-start : (x : start) → start
  norm-start x = x

  {-# TERMINATING #-}
  norm-sentence-star-11 : (x : sentence-star-11) → sentence-star-11
  norm-sentence-star-11 x = x

  {-# TERMINATING #-}
  norm-sentence-opt-9 : (x : sentence-opt-9) → sentence-opt-9
  norm-sentence-opt-9 x = x

  {-# TERMINATING #-}
  norm-sentence-bar-8 : (x : sentence-bar-8) → sentence-bar-8
  norm-sentence-bar-8 x = x

  {-# TERMINATING #-}
  norm-sentence-bar-7 : (x : sentence-bar-7) → sentence-bar-7
  norm-sentence-bar-7 x = x

  {-# TERMINATING #-}
  norm-sentence-bar-12 : (x : sentence-bar-12) → sentence-bar-12
  norm-sentence-bar-12 x = x

  {-# TERMINATING #-}
  norm-sentence-bar-10 : (x : sentence-bar-10) → sentence-bar-10
  norm-sentence-bar-10 x = x

  {-# TERMINATING #-}
  norm-sentence : (x : sentence) → sentence
  norm-sentence x = x

  {-# TERMINATING #-}
  norm-posinfo : (x : posinfo) → posinfo
  norm-posinfo x = x

  {-# TERMINATING #-}
  norm-paragraph-star-6 : (x : paragraph-star-6) → paragraph-star-6
  norm-paragraph-star-6 x = x

  {-# TERMINATING #-}
  norm-paragraph-bar-5 : (x : paragraph-bar-5) → paragraph-bar-5
  norm-paragraph-bar-5 x = x

  {-# TERMINATING #-}
  norm-paragraph-bar-4 : (x : paragraph-bar-4) → paragraph-bar-4
  norm-paragraph-bar-4 x = x

  {-# TERMINATING #-}
  norm-paragraph : (x : paragraph) → paragraph
  norm-paragraph x = x

  {-# TERMINATING #-}
  norm-cword : (x : cword) → cword
  norm-cword x = x

isParseTree : ParseTreeT → 𝕃 char → string → Set
isParseTree p l s = ⊤ {- this will be ignored since we are using simply typed runs -}

ptr : ParseTreeRec
ptr = record { ParseTreeT = ParseTreeT ; isParseTree = isParseTree ; ParseTreeToString = ParseTreeToString }

