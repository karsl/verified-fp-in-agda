module app where

open import lib

open import app-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _wss-star-5 : gratr2-nt
  _wss : gratr2-nt
  _ws-bar-4 : gratr2-nt
  _ws-bar-3 : gratr2-nt
  _ws : gratr2-nt
  _var-range-1 : gratr2-nt
  _var-plus-2 : gratr2-nt
  _var : gratr2-nt
  _start : gratr2-nt
  _posinfo : gratr2-nt
  _owss-opt-6 : gratr2-nt
  _owss : gratr2-nt
  _op : gratr2-nt
  _expr : gratr2-nt
  _cp : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _wss-star-5 _wss-star-5 = tt
gratr2-nt-eq  _wss _wss = tt
gratr2-nt-eq  _ws-bar-4 _ws-bar-4 = tt
gratr2-nt-eq  _ws-bar-3 _ws-bar-3 = tt
gratr2-nt-eq  _ws _ws = tt
gratr2-nt-eq  _var-range-1 _var-range-1 = tt
gratr2-nt-eq  _var-plus-2 _var-plus-2 = tt
gratr2-nt-eq  _var _var = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _owss-opt-6 _owss-opt-6 = tt
gratr2-nt-eq  _owss _owss = tt
gratr2-nt-eq  _op _op = tt
gratr2-nt-eq  _expr _expr = tt
gratr2-nt-eq  _cp _cp = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


app-start : gratr2-nt → 𝕃 gratr2-rule
app-start _wss-star-5 = (just "P35" , nothing , just _wss-star-5 , inj₁ _ws :: inj₁ _wss-star-5 :: []) :: (just "P34" , nothing , just _wss-star-5 , []) :: []
app-start _wss = (just "P36" , nothing , just _wss , inj₁ _wss-star-5 :: []) :: []
app-start _ws-bar-4 = (just "P32" , nothing , just _ws-bar-4 , inj₁ _ws-bar-3 :: []) :: (just "P31" , nothing , just _ws-bar-4 , inj₂ '\n' :: []) :: []
app-start _ws-bar-3 = (just "P30" , nothing , just _ws-bar-3 , inj₂ ' ' :: []) :: (just "P29" , nothing , just _ws-bar-3 , inj₂ '\t' :: []) :: []
app-start _ws = (just "P33" , nothing , just _ws , inj₁ _ws-bar-4 :: []) :: []
app-start _var-range-1 = (just "P9" , nothing , just _var-range-1 , inj₂ 'j' :: []) :: (just "P8" , nothing , just _var-range-1 , inj₂ 'i' :: []) :: (just "P7" , nothing , just _var-range-1 , inj₂ 'h' :: []) :: (just "P6" , nothing , just _var-range-1 , inj₂ 'g' :: []) :: (just "P5" , nothing , just _var-range-1 , inj₂ 'f' :: []) :: (just "P4" , nothing , just _var-range-1 , inj₂ 'e' :: []) :: (just "P3" , nothing , just _var-range-1 , inj₂ 'd' :: []) :: (just "P25" , nothing , just _var-range-1 , inj₂ 'z' :: []) :: (just "P24" , nothing , just _var-range-1 , inj₂ 'y' :: []) :: (just "P23" , nothing , just _var-range-1 , inj₂ 'x' :: []) :: (just "P22" , nothing , just _var-range-1 , inj₂ 'w' :: []) :: (just "P21" , nothing , just _var-range-1 , inj₂ 'v' :: []) :: (just "P20" , nothing , just _var-range-1 , inj₂ 'u' :: []) :: (just "P2" , nothing , just _var-range-1 , inj₂ 'c' :: []) :: (just "P19" , nothing , just _var-range-1 , inj₂ 't' :: []) :: (just "P18" , nothing , just _var-range-1 , inj₂ 's' :: []) :: (just "P17" , nothing , just _var-range-1 , inj₂ 'r' :: []) :: (just "P16" , nothing , just _var-range-1 , inj₂ 'q' :: []) :: (just "P15" , nothing , just _var-range-1 , inj₂ 'p' :: []) :: (just "P14" , nothing , just _var-range-1 , inj₂ 'o' :: []) :: (just "P13" , nothing , just _var-range-1 , inj₂ 'n' :: []) :: (just "P12" , nothing , just _var-range-1 , inj₂ 'm' :: []) :: (just "P11" , nothing , just _var-range-1 , inj₂ 'l' :: []) :: (just "P10" , nothing , just _var-range-1 , inj₂ 'k' :: []) :: (just "P1" , nothing , just _var-range-1 , inj₂ 'b' :: []) :: (just "P0" , nothing , just _var-range-1 , inj₂ 'a' :: []) :: []
app-start _var-plus-2 = (just "P27" , nothing , just _var-plus-2 , inj₁ _var-range-1 :: inj₁ _var-plus-2 :: []) :: (just "P26" , nothing , just _var-plus-2 , inj₁ _var-range-1 :: []) :: []
app-start _var = (just "P28" , nothing , just _var , inj₁ _var-plus-2 :: []) :: []
app-start _start = (just "Term" , just "Term_end" , just _start , inj₁ _owss :: inj₁ _expr :: inj₁ _owss :: []) :: []
app-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
app-start _owss-opt-6 = (just "P38" , nothing , just _owss-opt-6 , []) :: (just "P37" , nothing , just _owss-opt-6 , inj₁ _wss :: []) :: []
app-start _owss = (just "P39" , nothing , just _owss , inj₁ _owss-opt-6 :: []) :: []
app-start _op = (just "P40" , nothing , just _op , inj₂ '(' :: []) :: []
app-start _expr = (just "Var" , nothing , just _expr , inj₁ _var :: []) :: (just "Parens" , nothing , just _expr , inj₁ _op :: inj₁ _owss :: inj₁ _expr :: inj₁ _owss :: inj₁ _cp :: inj₁ _owss :: []) :: []
app-start _cp = (just "P41" , nothing , just _cp , inj₂ ')' :: []) :: []


app-return : maybe gratr2-nt → 𝕃 gratr2-rule
app-return (just _expr) = (nothing , nothing , just _expr , inj₁ _wss :: inj₁ _expr :: []) :: []
app-return _ = []

app-rtn : gratr2-rtn
app-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = app-start ; gratr2-return = app-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- App-} ((ParseTree (parsed-expr x0)) :: (ParseTree parsed-wss) :: _::_(ParseTree (parsed-expr x1)) rest) = just (ParseTree (parsed-expr (norm-expr (App x0 x1))) ::' rest , 3)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar 'a') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'a'))) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar 'b') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'b'))) ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(InputChar 'k') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'k'))) ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: _::_(InputChar 'l') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'l'))) ::' rest , 2)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(InputChar 'm') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'm'))) ::' rest , 2)
len-dec-rewrite {- P13-} ((Id "P13") :: _::_(InputChar 'n') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'n'))) ::' rest , 2)
len-dec-rewrite {- P14-} ((Id "P14") :: _::_(InputChar 'o') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'o'))) ::' rest , 2)
len-dec-rewrite {- P15-} ((Id "P15") :: _::_(InputChar 'p') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'p'))) ::' rest , 2)
len-dec-rewrite {- P16-} ((Id "P16") :: _::_(InputChar 'q') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'q'))) ::' rest , 2)
len-dec-rewrite {- P17-} ((Id "P17") :: _::_(InputChar 'r') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'r'))) ::' rest , 2)
len-dec-rewrite {- P18-} ((Id "P18") :: _::_(InputChar 's') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 's'))) ::' rest , 2)
len-dec-rewrite {- P19-} ((Id "P19") :: _::_(InputChar 't') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 't'))) ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar 'c') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'c'))) ::' rest , 2)
len-dec-rewrite {- P20-} ((Id "P20") :: _::_(InputChar 'u') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'u'))) ::' rest , 2)
len-dec-rewrite {- P21-} ((Id "P21") :: _::_(InputChar 'v') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'v'))) ::' rest , 2)
len-dec-rewrite {- P22-} ((Id "P22") :: _::_(InputChar 'w') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'w'))) ::' rest , 2)
len-dec-rewrite {- P23-} ((Id "P23") :: _::_(InputChar 'x') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'x'))) ::' rest , 2)
len-dec-rewrite {- P24-} ((Id "P24") :: _::_(InputChar 'y') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'y'))) ::' rest , 2)
len-dec-rewrite {- P25-} ((Id "P25") :: _::_(InputChar 'z') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'z'))) ::' rest , 2)
len-dec-rewrite {- P26-} ((Id "P26") :: _::_(ParseTree (parsed-var-range-1 x0)) rest) = just (ParseTree (parsed-var-plus-2 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P27-} ((Id "P27") :: (ParseTree (parsed-var-range-1 x0)) :: _::_(ParseTree (parsed-var-plus-2 x1)) rest) = just (ParseTree (parsed-var-plus-2 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P28-} ((Id "P28") :: _::_(ParseTree (parsed-var-plus-2 x0)) rest) = just (ParseTree (parsed-var (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P29-} ((Id "P29") :: _::_(InputChar '\t') rest) = just (ParseTree parsed-ws-bar-3 ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar 'd') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'd'))) ::' rest , 2)
len-dec-rewrite {- P30-} ((Id "P30") :: _::_(InputChar ' ') rest) = just (ParseTree parsed-ws-bar-3 ::' rest , 2)
len-dec-rewrite {- P31-} ((Id "P31") :: _::_(InputChar '\n') rest) = just (ParseTree parsed-ws-bar-4 ::' rest , 2)
len-dec-rewrite {- P32-} ((Id "P32") :: _::_(ParseTree parsed-ws-bar-3) rest) = just (ParseTree parsed-ws-bar-4 ::' rest , 2)
len-dec-rewrite {- P33-} ((Id "P33") :: _::_(ParseTree parsed-ws-bar-4) rest) = just (ParseTree parsed-ws ::' rest , 2)
len-dec-rewrite {- P35-} ((Id "P35") :: (ParseTree parsed-ws) :: _::_(ParseTree parsed-wss-star-5) rest) = just (ParseTree parsed-wss-star-5 ::' rest , 3)
len-dec-rewrite {- P36-} ((Id "P36") :: _::_(ParseTree parsed-wss-star-5) rest) = just (ParseTree parsed-wss ::' rest , 2)
len-dec-rewrite {- P37-} ((Id "P37") :: _::_(ParseTree parsed-wss) rest) = just (ParseTree parsed-owss-opt-6 ::' rest , 2)
len-dec-rewrite {- P39-} ((Id "P39") :: _::_(ParseTree parsed-owss-opt-6) rest) = just (ParseTree parsed-owss ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar 'e') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'e'))) ::' rest , 2)
len-dec-rewrite {- P40-} ((Id "P40") :: _::_(InputChar '(') rest) = just (ParseTree parsed-op ::' rest , 2)
len-dec-rewrite {- P41-} ((Id "P41") :: _::_(InputChar ')') rest) = just (ParseTree parsed-cp ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar 'f') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'f'))) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar 'g') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'g'))) ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar 'h') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'h'))) ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar 'i') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'i'))) ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar 'j') rest) = just (ParseTree (parsed-var-range-1 (string-append 0 (char-to-string 'j'))) ::' rest , 2)
len-dec-rewrite {- Parens-} ((Id "Parens") :: (ParseTree parsed-op) :: (ParseTree parsed-owss) :: (ParseTree (parsed-expr x0)) :: (ParseTree parsed-owss) :: (ParseTree parsed-cp) :: _::_(ParseTree parsed-owss) rest) = just (ParseTree (parsed-expr (norm-expr (Parens x0))) ::' rest , 7)
len-dec-rewrite {- Term-} ((Id "Term") :: (ParseTree parsed-owss) :: (ParseTree (parsed-expr x0)) :: (ParseTree parsed-owss) :: _::_(Id "Term_end") rest) = just (ParseTree (parsed-start (norm-start (Term x0))) ::' rest , 5)
len-dec-rewrite {- Var-} ((Id "Var") :: _::_(ParseTree (parsed-var x0)) rest) = just (ParseTree (parsed-expr (norm-expr (Var x0))) ::' rest , 2)
len-dec-rewrite {- P34-} (_::_(Id "P34") rest) = just (ParseTree parsed-wss-star-5 ::' rest , 1)
len-dec-rewrite {- P38-} (_::_(Id "P38") rest) = just (ParseTree parsed-owss-opt-6 ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
