module para where

open import lib

open import para-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _wss-star-18 : gratr2-nt
  _wss : gratr2-nt
  _ws-bar-17 : gratr2-nt
  _ws-bar-16 : gratr2-nt
  _ws : gratr2-nt
  _word-plus-13 : gratr2-nt
  _word : gratr2-nt
  _text-star-3 : gratr2-nt
  _text-bar-2 : gratr2-nt
  _text : gratr2-nt
  _start-opt-1 : gratr2-nt
  _start : gratr2-nt
  _sentence-star-11 : gratr2-nt
  _sentence-opt-9 : gratr2-nt
  _sentence-bar-8 : gratr2-nt
  _sentence-bar-7 : gratr2-nt
  _sentence-bar-12 : gratr2-nt
  _sentence-bar-10 : gratr2-nt
  _sentence : gratr2-nt
  _semicolon : gratr2-nt
  _qmark : gratr2-nt
  _posinfo : gratr2-nt
  _paragraph-star-6 : gratr2-nt
  _paragraph-bar-5 : gratr2-nt
  _paragraph-bar-4 : gratr2-nt
  _paragraph : gratr2-nt
  _owss-opt-19 : gratr2-nt
  _owss : gratr2-nt
  _nl : gratr2-nt
  _letter-range-15 : gratr2-nt
  _letter : gratr2-nt
  _dot : gratr2-nt
  _cword : gratr2-nt
  _comma : gratr2-nt
  _colon : gratr2-nt
  _cletter-range-14 : gratr2-nt
  _cletter : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _wss-star-18 _wss-star-18 = tt
gratr2-nt-eq  _wss _wss = tt
gratr2-nt-eq  _ws-bar-17 _ws-bar-17 = tt
gratr2-nt-eq  _ws-bar-16 _ws-bar-16 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _word-plus-13 _word-plus-13 = tt
gratr2-nt-eq  _word _word = tt
gratr2-nt-eq  _text-star-3 _text-star-3 = tt
gratr2-nt-eq  _text-bar-2 _text-bar-2 = tt
gratr2-nt-eq  _text _text = tt
gratr2-nt-eq  _start-opt-1 _start-opt-1 = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _sentence-star-11 _sentence-star-11 = tt
gratr2-nt-eq  _sentence-opt-9 _sentence-opt-9 = tt
gratr2-nt-eq  _sentence-bar-8 _sentence-bar-8 = tt
gratr2-nt-eq  _sentence-bar-7 _sentence-bar-7 = tt
gratr2-nt-eq  _sentence-bar-12 _sentence-bar-12 = tt
gratr2-nt-eq  _sentence-bar-10 _sentence-bar-10 = tt
gratr2-nt-eq  _sentence _sentence = tt
gratr2-nt-eq  _semicolon _semicolon = tt
gratr2-nt-eq  _qmark _qmark = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _paragraph-star-6 _paragraph-star-6 = tt
gratr2-nt-eq  _paragraph-bar-5 _paragraph-bar-5 = tt
gratr2-nt-eq  _paragraph-bar-4 _paragraph-bar-4 = tt
gratr2-nt-eq  _paragraph _paragraph = tt
gratr2-nt-eq  _owss-opt-19 _owss-opt-19 = tt
gratr2-nt-eq  _owss _owss = tt
gratr2-nt-eq  _nl _nl = tt
gratr2-nt-eq  _letter-range-15 _letter-range-15 = tt
gratr2-nt-eq  _letter _letter = tt
gratr2-nt-eq  _dot _dot = tt
gratr2-nt-eq  _cword _cword = tt
gratr2-nt-eq  _comma _comma = tt
gratr2-nt-eq  _colon _colon = tt
gratr2-nt-eq  _cletter-range-14 _cletter-range-14 = tt
gratr2-nt-eq  _cletter _cletter = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


para-start : gratr2-nt → 𝕃 gratr2-rule
para-start _wss-star-18 = (just "P87" , nothing , just _wss-star-18 , inj₁ _ws :: inj₁ _wss-star-18 :: []) :: (just "P86" , nothing , just _wss-star-18 , []) :: []
para-start _wss = (just "P88" , nothing , just _wss , inj₁ _wss-star-18 :: []) :: []
para-start _ws-bar-17 = (just "P84" , nothing , just _ws-bar-17 , inj₁ _ws-bar-16 :: []) :: (just "P83" , nothing , just _ws-bar-17 , inj₂ '\t' :: []) :: []
para-start _ws-bar-16 = (just "P82" , nothing , just _ws-bar-16 , inj₂ ' ' :: []) :: (just "P81" , nothing , just _ws-bar-16 , inj₂ '\n' :: []) :: []
para-start _ws = (just "P85" , nothing , just _ws , inj₁ _ws-bar-17 :: []) :: []
para-start _word-plus-13 = (just "Word-1" , nothing , just _word-plus-13 , inj₁ _letter :: inj₁ _word-plus-13 :: []) :: (just "Word-0" , nothing , just _word-plus-13 , inj₁ _letter :: []) :: []
para-start _word = (just "Word" , nothing , just _word , inj₁ _word-plus-13 :: []) :: []
para-start _text-star-3 = (just "Text-3" , nothing , just _text-star-3 , inj₁ _text-bar-2 :: inj₁ _paragraph :: inj₁ _text-star-3 :: []) :: (just "Text-2" , nothing , just _text-star-3 , []) :: []
para-start _text-bar-2 = (just "Text-1" , nothing , just _text-bar-2 , inj₁ _nl :: inj₁ _nl :: []) :: (just "Text-0" , nothing , just _text-bar-2 , inj₁ _nl :: []) :: []
para-start _text = (just "Text" , nothing , just _text , inj₁ _paragraph :: inj₁ _text-star-3 :: []) :: []
para-start _start-opt-1 = (just "Start-1" , nothing , just _start-opt-1 , []) :: (just "Start-0" , nothing , just _start-opt-1 , inj₁ _nl :: []) :: []
para-start _start = (just "Start" , nothing , just _start , inj₁ _text :: inj₁ _start-opt-1 :: []) :: []
para-start _sentence-star-11 = (just "Sentence-9" , nothing , just _sentence-star-11 , inj₁ _sentence-opt-9 :: inj₁ _sentence-bar-10 :: inj₁ _word :: inj₁ _sentence-star-11 :: []) :: (just "Sentence-8" , nothing , just _sentence-star-11 , []) :: []
para-start _sentence-opt-9 = (just "Sentence-5" , nothing , just _sentence-opt-9 , []) :: (just "Sentence-4" , nothing , just _sentence-opt-9 , inj₁ _sentence-bar-8 :: []) :: []
para-start _sentence-bar-8 = (just "Sentence-3" , nothing , just _sentence-bar-8 , inj₁ _sentence-bar-7 :: []) :: (just "Sentence-2" , nothing , just _sentence-bar-8 , inj₁ _comma :: []) :: []
para-start _sentence-bar-7 = (just "Sentence-1" , nothing , just _sentence-bar-7 , inj₁ _semicolon :: []) :: (just "Sentence-0" , nothing , just _sentence-bar-7 , inj₁ _colon :: []) :: []
para-start _sentence-bar-12 = (just "Sentence-11" , nothing , just _sentence-bar-12 , inj₁ _dot :: []) :: (just "Sentence-10" , nothing , just _sentence-bar-12 , inj₁ _qmark :: []) :: []
para-start _sentence-bar-10 = (just "Sentence-7" , nothing , just _sentence-bar-10 , inj₁ _nl :: []) :: (just "Sentence-6" , nothing , just _sentence-bar-10 , inj₂ ' ' :: []) :: []
para-start _sentence = (just "Sentence" , nothing , just _sentence , inj₁ _cword :: inj₁ _sentence-star-11 :: inj₁ _sentence-bar-12 :: []) :: []
para-start _semicolon = (just "P94" , nothing , just _semicolon , inj₂ ';' :: []) :: []
para-start _qmark = (just "P95" , nothing , just _qmark , inj₂ '?' :: []) :: []
para-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
para-start _paragraph-star-6 = (just "Paragraph-5" , nothing , just _paragraph-star-6 , inj₁ _paragraph-bar-5 :: inj₁ _sentence :: inj₁ _paragraph-star-6 :: []) :: (just "Paragraph-4" , nothing , just _paragraph-star-6 , []) :: []
para-start _paragraph-bar-5 = (just "Paragraph-3" , nothing , just _paragraph-bar-5 , inj₁ _paragraph-bar-4 :: []) :: (just "Paragraph-2" , nothing , just _paragraph-bar-5 , inj₂ ' ' :: []) :: []
para-start _paragraph-bar-4 = (just "Paragraph-1" , nothing , just _paragraph-bar-4 , inj₁ _nl :: []) :: (just "Paragraph-0" , nothing , just _paragraph-bar-4 , inj₂ ' ' :: inj₂ ' ' :: []) :: []
para-start _paragraph = (just "Paragraph" , nothing , just _paragraph , inj₁ _sentence :: inj₁ _paragraph-star-6 :: []) :: []
para-start _owss-opt-19 = (just "P90" , nothing , just _owss-opt-19 , []) :: (just "P89" , nothing , just _owss-opt-19 , inj₁ _wss :: []) :: []
para-start _owss = (just "P91" , nothing , just _owss , inj₁ _owss-opt-19 :: []) :: []
para-start _nl = (just "P80" , nothing , just _nl , inj₂ '\n' :: []) :: []
para-start _letter-range-15 = (just "P78" , nothing , just _letter-range-15 , inj₂ 'z' :: []) :: (just "P77" , nothing , just _letter-range-15 , inj₂ 'y' :: []) :: (just "P76" , nothing , just _letter-range-15 , inj₂ 'x' :: []) :: (just "P75" , nothing , just _letter-range-15 , inj₂ 'w' :: []) :: (just "P74" , nothing , just _letter-range-15 , inj₂ 'v' :: []) :: (just "P73" , nothing , just _letter-range-15 , inj₂ 'u' :: []) :: (just "P72" , nothing , just _letter-range-15 , inj₂ 't' :: []) :: (just "P71" , nothing , just _letter-range-15 , inj₂ 's' :: []) :: (just "P70" , nothing , just _letter-range-15 , inj₂ 'r' :: []) :: (just "P69" , nothing , just _letter-range-15 , inj₂ 'q' :: []) :: (just "P68" , nothing , just _letter-range-15 , inj₂ 'p' :: []) :: (just "P67" , nothing , just _letter-range-15 , inj₂ 'o' :: []) :: (just "P66" , nothing , just _letter-range-15 , inj₂ 'n' :: []) :: (just "P65" , nothing , just _letter-range-15 , inj₂ 'm' :: []) :: (just "P64" , nothing , just _letter-range-15 , inj₂ 'l' :: []) :: (just "P63" , nothing , just _letter-range-15 , inj₂ 'k' :: []) :: (just "P62" , nothing , just _letter-range-15 , inj₂ 'j' :: []) :: (just "P61" , nothing , just _letter-range-15 , inj₂ 'i' :: []) :: (just "P60" , nothing , just _letter-range-15 , inj₂ 'h' :: []) :: (just "P59" , nothing , just _letter-range-15 , inj₂ 'g' :: []) :: (just "P58" , nothing , just _letter-range-15 , inj₂ 'f' :: []) :: (just "P57" , nothing , just _letter-range-15 , inj₂ 'e' :: []) :: (just "P56" , nothing , just _letter-range-15 , inj₂ 'd' :: []) :: (just "P55" , nothing , just _letter-range-15 , inj₂ 'c' :: []) :: (just "P54" , nothing , just _letter-range-15 , inj₂ 'b' :: []) :: (just "P53" , nothing , just _letter-range-15 , inj₂ 'a' :: []) :: (just "P52" , nothing , just _letter-range-15 , inj₂ 'Z' :: []) :: (just "P51" , nothing , just _letter-range-15 , inj₂ 'Y' :: []) :: (just "P50" , nothing , just _letter-range-15 , inj₂ 'X' :: []) :: (just "P49" , nothing , just _letter-range-15 , inj₂ 'W' :: []) :: (just "P48" , nothing , just _letter-range-15 , inj₂ 'V' :: []) :: (just "P47" , nothing , just _letter-range-15 , inj₂ 'U' :: []) :: (just "P46" , nothing , just _letter-range-15 , inj₂ 'T' :: []) :: (just "P45" , nothing , just _letter-range-15 , inj₂ 'S' :: []) :: (just "P44" , nothing , just _letter-range-15 , inj₂ 'R' :: []) :: (just "P43" , nothing , just _letter-range-15 , inj₂ 'Q' :: []) :: (just "P42" , nothing , just _letter-range-15 , inj₂ 'P' :: []) :: (just "P41" , nothing , just _letter-range-15 , inj₂ 'O' :: []) :: (just "P40" , nothing , just _letter-range-15 , inj₂ 'N' :: []) :: (just "P39" , nothing , just _letter-range-15 , inj₂ 'M' :: []) :: (just "P38" , nothing , just _letter-range-15 , inj₂ 'L' :: []) :: (just "P37" , nothing , just _letter-range-15 , inj₂ 'K' :: []) :: (just "P36" , nothing , just _letter-range-15 , inj₂ 'J' :: []) :: (just "P35" , nothing , just _letter-range-15 , inj₂ 'I' :: []) :: (just "P34" , nothing , just _letter-range-15 , inj₂ 'H' :: []) :: (just "P33" , nothing , just _letter-range-15 , inj₂ 'G' :: []) :: (just "P32" , nothing , just _letter-range-15 , inj₂ 'F' :: []) :: (just "P31" , nothing , just _letter-range-15 , inj₂ 'E' :: []) :: (just "P30" , nothing , just _letter-range-15 , inj₂ 'D' :: []) :: (just "P29" , nothing , just _letter-range-15 , inj₂ 'C' :: []) :: (just "P28" , nothing , just _letter-range-15 , inj₂ 'B' :: []) :: (just "P27" , nothing , just _letter-range-15 , inj₂ 'A' :: []) :: []
para-start _letter = (just "P79" , nothing , just _letter , inj₁ _letter-range-15 :: []) :: []
para-start _dot = (just "P96" , nothing , just _dot , inj₂ '.' :: []) :: []
para-start _cword = (just "CWord" , nothing , just _cword , inj₁ _cletter :: inj₁ _word :: []) :: []
para-start _comma = (just "P92" , nothing , just _comma , inj₂ ',' :: []) :: []
para-start _colon = (just "P93" , nothing , just _colon , inj₂ ':' :: []) :: []
para-start _cletter-range-14 = (just "P9" , nothing , just _cletter-range-14 , inj₂ 'J' :: []) :: (just "P8" , nothing , just _cletter-range-14 , inj₂ 'I' :: []) :: (just "P7" , nothing , just _cletter-range-14 , inj₂ 'H' :: []) :: (just "P6" , nothing , just _cletter-range-14 , inj₂ 'G' :: []) :: (just "P5" , nothing , just _cletter-range-14 , inj₂ 'F' :: []) :: (just "P4" , nothing , just _cletter-range-14 , inj₂ 'E' :: []) :: (just "P3" , nothing , just _cletter-range-14 , inj₂ 'D' :: []) :: (just "P25" , nothing , just _cletter-range-14 , inj₂ 'Z' :: []) :: (just "P24" , nothing , just _cletter-range-14 , inj₂ 'Y' :: []) :: (just "P23" , nothing , just _cletter-range-14 , inj₂ 'X' :: []) :: (just "P22" , nothing , just _cletter-range-14 , inj₂ 'W' :: []) :: (just "P21" , nothing , just _cletter-range-14 , inj₂ 'V' :: []) :: (just "P20" , nothing , just _cletter-range-14 , inj₂ 'U' :: []) :: (just "P2" , nothing , just _cletter-range-14 , inj₂ 'C' :: []) :: (just "P19" , nothing , just _cletter-range-14 , inj₂ 'T' :: []) :: (just "P18" , nothing , just _cletter-range-14 , inj₂ 'S' :: []) :: (just "P17" , nothing , just _cletter-range-14 , inj₂ 'R' :: []) :: (just "P16" , nothing , just _cletter-range-14 , inj₂ 'Q' :: []) :: (just "P15" , nothing , just _cletter-range-14 , inj₂ 'P' :: []) :: (just "P14" , nothing , just _cletter-range-14 , inj₂ 'O' :: []) :: (just "P13" , nothing , just _cletter-range-14 , inj₂ 'N' :: []) :: (just "P12" , nothing , just _cletter-range-14 , inj₂ 'M' :: []) :: (just "P11" , nothing , just _cletter-range-14 , inj₂ 'L' :: []) :: (just "P10" , nothing , just _cletter-range-14 , inj₂ 'K' :: []) :: (just "P1" , nothing , just _cletter-range-14 , inj₂ 'B' :: []) :: (just "P0" , nothing , just _cletter-range-14 , inj₂ 'A' :: []) :: []
para-start _cletter = (just "P26" , nothing , just _cletter , inj₁ _cletter-range-14 :: []) :: []


para-return : maybe gratr2-nt → 𝕃 gratr2-rule
para-return _ = []

para-rtn : gratr2-rtn
para-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = para-start ; gratr2-return = para-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- CWord-} ((Id "CWord") :: (ParseTree parsed-cletter) :: _::_(ParseTree (parsed-word x0)) rest) = just (ParseTree (parsed-cword (norm-cword (CWord x0))) ::' rest , 3)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'A') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'B') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'K') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'L') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'M') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'N') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'O') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'P') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'Q') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'R') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 'S') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 'T') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'C') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'U') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'V') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'W') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'X') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'Y') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'Z') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(ParseTree parsed-cletter-range-14) rest) = just (ParseTree parsed-cletter ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: _::_(InputChar 'A') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(InputChar 'B') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar 'C') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'D') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar 'D') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar 'E') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(InputChar 'F') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(InputChar 'G') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P34-} ((Id "P34") :: _::_(InputChar 'H') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: _::_(InputChar 'I') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(InputChar 'J') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(InputChar 'K') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P38-} ((Id "P38") :: _::_(InputChar 'L') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(InputChar 'M') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'E') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar 'N') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar 'O') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P42-} ((Id "P42") :: _::_(InputChar 'P') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P43-} ((Id "P43") :: _::_(InputChar 'Q') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P44-} ((Id "P44") :: _::_(InputChar 'R') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P45-} ((Id "P45") :: _::_(InputChar 'S') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P46-} ((Id "P46") :: _::_(InputChar 'T') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P47-} ((Id "P47") :: _::_(InputChar 'U') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P48-} ((Id "P48") :: _::_(InputChar 'V') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P49-} ((Id "P49") :: _::_(InputChar 'W') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'F') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P50-} ((Id "P50") :: _::_(InputChar 'X') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P51-} ((Id "P51") :: _::_(InputChar 'Y') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P52-} ((Id "P52") :: _::_(InputChar 'Z') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P53-} ((Id "P53") :: _::_(InputChar 'a') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P54-} ((Id "P54") :: _::_(InputChar 'b') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P55-} ((Id "P55") :: _::_(InputChar 'c') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P56-} ((Id "P56") :: _::_(InputChar 'd') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P57-} ((Id "P57") :: _::_(InputChar 'e') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P58-} ((Id "P58") :: _::_(InputChar 'f') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P59-} ((Id "P59") :: _::_(InputChar 'g') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'G') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P60-} ((Id "P60") :: _::_(InputChar 'h') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P61-} ((Id "P61") :: _::_(InputChar 'i') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P62-} ((Id "P62") :: _::_(InputChar 'j') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P63-} ((Id "P63") :: _::_(InputChar 'k') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P64-} ((Id "P64") :: _::_(InputChar 'l') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P65-} ((Id "P65") :: _::_(InputChar 'm') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P66-} ((Id "P66") :: _::_(InputChar 'n') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P67-} ((Id "P67") :: _::_(InputChar 'o') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P68-} ((Id "P68") :: _::_(InputChar 'p') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P69-} ((Id "P69") :: _::_(InputChar 'q') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'H') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P70-} ((Id "P70") :: _::_(InputChar 'r') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P71-} ((Id "P71") :: _::_(InputChar 's') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P72-} ((Id "P72") :: _::_(InputChar 't') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P73-} ((Id "P73") :: _::_(InputChar 'u') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P74-} ((Id "P74") :: _::_(InputChar 'v') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P75-} ((Id "P75") :: _::_(InputChar 'w') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P76-} ((Id "P76") :: _::_(InputChar 'x') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P77-} ((Id "P77") :: _::_(InputChar 'y') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P78-} ((Id "P78") :: _::_(InputChar 'z') rest) = just (ParseTree parsed-letter-range-15 ::' rest , 2)
len-dec-rewrite {- P79-} ((Id "P79") :: _::_(ParseTree parsed-letter-range-15) rest) = just (ParseTree parsed-letter ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'I') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P80-} ((Id "P80") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-nl ::' rest , 2)
len-dec-rewrite {- P81-} ((Id "P81") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-ws-bar-16 ::' rest , 2)
len-dec-rewrite {- P82-} ((Id "P82") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-ws-bar-16 ::' rest , 2)
len-dec-rewrite {- P83-} ((Id "P83") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-ws-bar-17 ::' rest , 2)
len-dec-rewrite {- P84-} ((Id "P84") :: _::_(ParseTree parsed-ws-bar-16) rest) = just (ParseTree parsed-ws-bar-17 ::' rest , 2)
len-dec-rewrite {- P85-} ((Id "P85") :: _::_(ParseTree parsed-ws-bar-17) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P87-} ((Id "P87") :: (ParseTree parsed-ws) :: _::_(ParseTree parsed-wss-star-18) rest) = just (ParseTree parsed-wss-star-18 ::' rest , 3)
len-dec-rewrite {- P88-} ((Id "P88") :: _::_(ParseTree parsed-wss-star-18) rest) = just (ParseTree parsed-wss ::' rest , 2)
len-dec-rewrite {- P89-} ((Id "P89") :: _::_(ParseTree parsed-wss) rest) = just (ParseTree parsed-owss-opt-19 ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'J') rest) = just (ParseTree parsed-cletter-range-14 ::' rest , 2)
len-dec-rewrite {- P91-} ((Id "P91") :: _::_(ParseTree parsed-owss-opt-19) rest) = just (ParseTree parsed-owss ::' rest , 2)
len-dec-rewrite {- P92-} ((Id "P92") :: _::_(InputChar ',') rest) = just (ParseTree parsed-comma ::' rest , 2)
len-dec-rewrite {- P93-} ((Id "P93") :: _::_(InputChar ':') rest) = just (ParseTree parsed-colon ::' rest , 2)
len-dec-rewrite {- P94-} ((Id "P94") :: _::_(InputChar ';') rest) = just (ParseTree parsed-semicolon ::' rest , 2)
len-dec-rewrite {- P95-} ((Id "P95") :: _::_(InputChar '?') rest) = just (ParseTree parsed-qmark ::' rest , 2)
len-dec-rewrite {- P96-} ((Id "P96") :: _::_(InputChar '.') rest) = just (ParseTree parsed-dot ::' rest , 2)
len-dec-rewrite {- Paragraph-} ((Id "Paragraph") :: (ParseTree (parsed-sentence x0)) :: _::_(ParseTree (parsed-paragraph-star-6 x1)) rest) = just (ParseTree (parsed-paragraph (norm-paragraph (Paragraph x0 x1))) ::' rest , 3)
len-dec-rewrite {- Paragraph-0-} ((Id "Paragraph-0") :: (InputChar ' ') :: _::_(InputChar ' ') rest) = just (ParseTree (parsed-paragraph-bar-4 (norm-paragraph-bar-4 Paragraph-0)) ::' rest , 3)
len-dec-rewrite {- Paragraph-1-} ((Id "Paragraph-1") :: _::_(ParseTree parsed-nl) rest) = just (ParseTree (parsed-paragraph-bar-4 (norm-paragraph-bar-4 Paragraph-1)) ::' rest , 2)
len-dec-rewrite {- Paragraph-2-} ((Id "Paragraph-2") :: _::_(InputChar ' ') rest) = just (ParseTree (parsed-paragraph-bar-5 (norm-paragraph-bar-5 Paragraph-2)) ::' rest , 2)
len-dec-rewrite {- Paragraph-3-} ((Id "Paragraph-3") :: _::_(ParseTree (parsed-paragraph-bar-4 x0)) rest) = just (ParseTree (parsed-paragraph-bar-5 (norm-paragraph-bar-5 (Paragraph-3 x0))) ::' rest , 2)
len-dec-rewrite {- Paragraph-5-} ((Id "Paragraph-5") :: (ParseTree (parsed-paragraph-bar-5 x0)) :: (ParseTree (parsed-sentence x1)) :: _::_(ParseTree (parsed-paragraph-star-6 x2)) rest) = just (ParseTree (parsed-paragraph-star-6 (norm-paragraph-star-6 (Paragraph-5 x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- Sentence-} ((Id "Sentence") :: (ParseTree (parsed-cword x0)) :: (ParseTree (parsed-sentence-star-11 x1)) :: _::_(ParseTree (parsed-sentence-bar-12 x2)) rest) = just (ParseTree (parsed-sentence (norm-sentence (Sentence x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- Sentence-0-} ((Id "Sentence-0") :: _::_(ParseTree parsed-colon) rest) = just (ParseTree (parsed-sentence-bar-7 (norm-sentence-bar-7 Sentence-0)) ::' rest , 2)
len-dec-rewrite {- Sentence-1-} ((Id "Sentence-1") :: _::_(ParseTree parsed-semicolon) rest) = just (ParseTree (parsed-sentence-bar-7 (norm-sentence-bar-7 Sentence-1)) ::' rest , 2)
len-dec-rewrite {- Sentence-10-} ((Id "Sentence-10") :: _::_(ParseTree parsed-qmark) rest) = just (ParseTree (parsed-sentence-bar-12 (norm-sentence-bar-12 Sentence-10)) ::' rest , 2)
len-dec-rewrite {- Sentence-11-} ((Id "Sentence-11") :: _::_(ParseTree parsed-dot) rest) = just (ParseTree (parsed-sentence-bar-12 (norm-sentence-bar-12 Sentence-11)) ::' rest , 2)
len-dec-rewrite {- Sentence-2-} ((Id "Sentence-2") :: _::_(ParseTree parsed-comma) rest) = just (ParseTree (parsed-sentence-bar-8 (norm-sentence-bar-8 Sentence-2)) ::' rest , 2)
len-dec-rewrite {- Sentence-3-} ((Id "Sentence-3") :: _::_(ParseTree (parsed-sentence-bar-7 x0)) rest) = just (ParseTree (parsed-sentence-bar-8 (norm-sentence-bar-8 (Sentence-3 x0))) ::' rest , 2)
len-dec-rewrite {- Sentence-4-} ((Id "Sentence-4") :: _::_(ParseTree (parsed-sentence-bar-8 x0)) rest) = just (ParseTree (parsed-sentence-opt-9 (norm-sentence-opt-9 (Sentence-4 x0))) ::' rest , 2)
len-dec-rewrite {- Sentence-6-} ((Id "Sentence-6") :: _::_(InputChar ' ') rest) = just (ParseTree (parsed-sentence-bar-10 (norm-sentence-bar-10 Sentence-6)) ::' rest , 2)
len-dec-rewrite {- Sentence-7-} ((Id "Sentence-7") :: _::_(ParseTree parsed-nl) rest) = just (ParseTree (parsed-sentence-bar-10 (norm-sentence-bar-10 Sentence-7)) ::' rest , 2)
len-dec-rewrite {- Sentence-9-} ((Id "Sentence-9") :: (ParseTree (parsed-sentence-opt-9 x0)) :: (ParseTree (parsed-sentence-bar-10 x1)) :: (ParseTree (parsed-word x2)) :: _::_(ParseTree (parsed-sentence-star-11 x3)) rest) = just (ParseTree (parsed-sentence-star-11 (norm-sentence-star-11 (Sentence-9 x0 x1 x2 x3))) ::' rest , 5)
len-dec-rewrite {- Start-} ((Id "Start") :: (ParseTree (parsed-text x0)) :: _::_(ParseTree (parsed-start-opt-1 x1)) rest) = just (ParseTree (parsed-start (norm-start (Start x0 x1))) ::' rest , 3)
len-dec-rewrite {- Start-0-} ((Id "Start-0") :: _::_(ParseTree parsed-nl) rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Start-0)) ::' rest , 2)
len-dec-rewrite {- Text-} ((Id "Text") :: (ParseTree (parsed-paragraph x0)) :: _::_(ParseTree (parsed-text-star-3 x1)) rest) = just (ParseTree (parsed-text (norm-text (Text x0 x1))) ::' rest , 3)
len-dec-rewrite {- Text-0-} ((Id "Text-0") :: _::_(ParseTree parsed-nl) rest) = just (ParseTree (parsed-text-bar-2 (norm-text-bar-2 Text-0)) ::' rest , 2)
len-dec-rewrite {- Text-1-} ((Id "Text-1") :: (ParseTree parsed-nl) :: _::_(ParseTree parsed-nl) rest) = just (ParseTree (parsed-text-bar-2 (norm-text-bar-2 Text-1)) ::' rest , 3)
len-dec-rewrite {- Text-3-} ((Id "Text-3") :: (ParseTree (parsed-text-bar-2 x0)) :: (ParseTree (parsed-paragraph x1)) :: _::_(ParseTree (parsed-text-star-3 x2)) rest) = just (ParseTree (parsed-text-star-3 (norm-text-star-3 (Text-3 x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- Word-} ((Id "Word") :: _::_(ParseTree (parsed-word-plus-13 x0)) rest) = just (ParseTree (parsed-word (norm-word (Word x0))) ::' rest , 2)
len-dec-rewrite {- Word-0-} ((Id "Word-0") :: _::_(ParseTree parsed-letter) rest) = just (ParseTree (parsed-word-plus-13 (norm-word-plus-13 Word-0)) ::' rest , 2)
len-dec-rewrite {- Word-1-} ((Id "Word-1") :: (ParseTree parsed-letter) :: _::_(ParseTree (parsed-word-plus-13 x0)) rest) = just (ParseTree (parsed-word-plus-13 (norm-word-plus-13 (Word-1 x0))) ::' rest , 3)
len-dec-rewrite {- P86-} (_::_(Id "P86") rest) = just (ParseTree parsed-wss-star-18 ::' rest , 1)
len-dec-rewrite {- P90-} (_::_(Id "P90") rest) = just (ParseTree parsed-owss-opt-19 ::' rest , 1)
len-dec-rewrite {- Paragraph-4-} (_::_(Id "Paragraph-4") rest) = just (ParseTree (parsed-paragraph-star-6 (norm-paragraph-star-6 Paragraph-4)) ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite {- Sentence-5-} (_::_(Id "Sentence-5") rest) = just (ParseTree (parsed-sentence-opt-9 (norm-sentence-opt-9 Sentence-5)) ::' rest , 1)
len-dec-rewrite {- Sentence-8-} (_::_(Id "Sentence-8") rest) = just (ParseTree (parsed-sentence-star-11 (norm-sentence-star-11 Sentence-8)) ::' rest , 1)
len-dec-rewrite {- Start-1-} (_::_(Id "Start-1") rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Start-1)) ::' rest , 1)
len-dec-rewrite {- Text-2-} (_::_(Id "Text-2") rest) = just (ParseTree (parsed-text-star-3 (norm-text-star-3 Text-2)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
