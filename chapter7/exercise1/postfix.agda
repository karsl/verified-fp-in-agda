module postfix where

open import lib

open import postfix-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _start-opt-1 : gratr2-nt
  _start : gratr2-nt
  _postfix : gratr2-nt
  _posinfo : gratr2-nt
  _num-range-2 : gratr2-nt
  _num-plus-3 : gratr2-nt
  _num : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _start-opt-1 _start-opt-1 = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _postfix _postfix = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _num-range-2 _num-range-2 = tt
gratr2-nt-eq  _num-plus-3 _num-plus-3 = tt
gratr2-nt-eq  _num _num = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


postfix-start : gratr2-nt → 𝕃 gratr2-rule
postfix-start _start-opt-1 = (just "Postfix-1" , nothing , just _start-opt-1 , []) :: (just "Postfix-0" , nothing , just _start-opt-1 , inj₂ '\n' :: []) :: []
postfix-start _start = (just "Postfix" , just "Postfix_end" , just _start , inj₁ _postfix :: inj₁ _start-opt-1 :: []) :: []
postfix-start _postfix = (just "Num" , nothing , just _postfix , inj₁ _num :: []) :: []
postfix-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
postfix-start _num-range-2 = (just "P9" , nothing , just _num-range-2 , inj₂ '9' :: []) :: (just "P8" , nothing , just _num-range-2 , inj₂ '8' :: []) :: (just "P7" , nothing , just _num-range-2 , inj₂ '7' :: []) :: (just "P6" , nothing , just _num-range-2 , inj₂ '6' :: []) :: (just "P5" , nothing , just _num-range-2 , inj₂ '5' :: []) :: (just "P4" , nothing , just _num-range-2 , inj₂ '4' :: []) :: (just "P3" , nothing , just _num-range-2 , inj₂ '3' :: []) :: (just "P2" , nothing , just _num-range-2 , inj₂ '2' :: []) :: (just "P1" , nothing , just _num-range-2 , inj₂ '1' :: []) :: (just "P0" , nothing , just _num-range-2 , inj₂ '0' :: []) :: []
postfix-start _num-plus-3 = (just "P11" , nothing , just _num-plus-3 , inj₁ _num-range-2 :: inj₁ _num-plus-3 :: []) :: (just "P10" , nothing , just _num-plus-3 , inj₁ _num-range-2 :: []) :: []
postfix-start _num = (just "P12" , nothing , just _num , inj₁ _num-plus-3 :: []) :: []


postfix-return : maybe gratr2-nt → 𝕃 gratr2-rule
postfix-return (just _postfix) = (nothing , nothing , just _postfix , inj₂ ' ' :: inj₁ _postfix :: inj₂ '+' :: []) :: []
postfix-return _ = []

postfix-rtn : gratr2-rtn
postfix-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = postfix-start ; gratr2-return = postfix-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- Num-} ((Id "Num") :: _::_(ParseTree (parsed-num x0)) rest) = just (ParseTree (parsed-postfix (norm-postfix (Num x0))) ::' rest , 2)
len-dec-rewrite {- P0-} ((Id "P0") :: _::_(InputChar '0') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '0'))) ::' rest , 2)
len-dec-rewrite {- P1-} ((Id "P1") :: _::_(InputChar '1') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '1'))) ::' rest , 2)
len-dec-rewrite {- P10-} ((Id "P10") :: _::_(ParseTree (parsed-num-range-2 x0)) rest) = just (ParseTree (parsed-num-plus-3 (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P11-} ((Id "P11") :: (ParseTree (parsed-num-range-2 x0)) :: _::_(ParseTree (parsed-num-plus-3 x1)) rest) = just (ParseTree (parsed-num-plus-3 (string-append 1 x0 x1)) ::' rest , 3)
len-dec-rewrite {- P12-} ((Id "P12") :: _::_(ParseTree (parsed-num-plus-3 x0)) rest) = just (ParseTree (parsed-num (string-append 0 x0)) ::' rest , 2)
len-dec-rewrite {- P2-} ((Id "P2") :: _::_(InputChar '2') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '2'))) ::' rest , 2)
len-dec-rewrite {- P3-} ((Id "P3") :: _::_(InputChar '3') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '3'))) ::' rest , 2)
len-dec-rewrite {- P4-} ((Id "P4") :: _::_(InputChar '4') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '4'))) ::' rest , 2)
len-dec-rewrite {- P5-} ((Id "P5") :: _::_(InputChar '5') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '5'))) ::' rest , 2)
len-dec-rewrite {- P6-} ((Id "P6") :: _::_(InputChar '6') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '6'))) ::' rest , 2)
len-dec-rewrite {- P7-} ((Id "P7") :: _::_(InputChar '7') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '7'))) ::' rest , 2)
len-dec-rewrite {- P8-} ((Id "P8") :: _::_(InputChar '8') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '8'))) ::' rest , 2)
len-dec-rewrite {- P9-} ((Id "P9") :: _::_(InputChar '9') rest) = just (ParseTree (parsed-num-range-2 (string-append 0 (char-to-string '9'))) ::' rest , 2)
len-dec-rewrite {- Plus-} ((ParseTree (parsed-postfix x0)) :: (InputChar ' ') :: (ParseTree (parsed-postfix x1)) :: _::_(InputChar '+') rest) = just (ParseTree (parsed-postfix (norm-postfix (Plus x0 x1))) ::' rest , 4)
len-dec-rewrite {- Postfix-} ((Id "Postfix") :: (ParseTree (parsed-postfix x0)) :: (ParseTree (parsed-start-opt-1 x1)) :: _::_(Id "Postfix_end") rest) = just (ParseTree (parsed-start (norm-start (Postfix x0 x1))) ::' rest , 4)
len-dec-rewrite {- Postfix-0-} ((Id "Postfix-0") :: _::_(InputChar '\n') rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Postfix-0)) ::' rest , 2)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite {- Postfix-1-} (_::_(Id "Postfix-1") rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Postfix-1)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
