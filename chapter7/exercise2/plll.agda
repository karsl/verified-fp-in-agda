module plll where

open import lib

open import plll-types public
----------------------------------------------------------------------------------
-- Run-rewriting rules
----------------------------------------------------------------------------------

data gratr2-nt : Set where
  _start-opt-1 : gratr2-nt
  _start : gratr2-nt
  _posinfo : gratr2-nt
  _listt-bar-2 : gratr2-nt
  _listt : gratr2-nt
  _list-seq-star-8 : gratr2-nt
  _list-seq-star-7 : gratr2-nt
  _list-seq-star-6 : gratr2-nt
  _list-seq-star-5 : gratr2-nt
  _list-seq : gratr2-nt
  _list-lit : gratr2-nt
  _list-comma-star-4 : gratr2-nt
  _list-comma-star-3 : gratr2-nt
  _list-comma : gratr2-nt


gratr2-nt-eq : gratr2-nt → gratr2-nt → 𝔹
gratr2-nt-eq  _start-opt-1 _start-opt-1 = tt
gratr2-nt-eq  _start _start = tt
gratr2-nt-eq  _posinfo _posinfo = tt
gratr2-nt-eq  _listt-bar-2 _listt-bar-2 = tt
gratr2-nt-eq  _listt _listt = tt
gratr2-nt-eq  _list-seq-star-8 _list-seq-star-8 = tt
gratr2-nt-eq  _list-seq-star-7 _list-seq-star-7 = tt
gratr2-nt-eq  _list-seq-star-6 _list-seq-star-6 = tt
gratr2-nt-eq  _list-seq-star-5 _list-seq-star-5 = tt
gratr2-nt-eq  _list-seq _list-seq = tt
gratr2-nt-eq  _list-lit _list-lit = tt
gratr2-nt-eq  _list-comma-star-4 _list-comma-star-4 = tt
gratr2-nt-eq  _list-comma-star-3 _list-comma-star-3 = tt
gratr2-nt-eq  _list-comma _list-comma = tt
gratr2-nt-eq _ _ = ff


open import rtn gratr2-nt


plll-start : gratr2-nt → 𝕃 gratr2-rule
plll-start _start-opt-1 = (just "Start-1" , nothing , just _start-opt-1 , []) :: (just "Start-0" , nothing , just _start-opt-1 , inj₂ '\n' :: []) :: []
plll-start _start = (just "Start" , nothing , just _start , inj₁ _listt :: inj₁ _start-opt-1 :: []) :: []
plll-start _posinfo = (just "Posinfo" , nothing , just _posinfo , []) :: []
plll-start _listt-bar-2 = (just "Listt-1" , nothing , just _listt-bar-2 , inj₁ _list-lit :: []) :: (just "Listt-0" , nothing , just _listt-bar-2 , inj₁ _list-comma :: []) :: []
plll-start _listt = (just "Listt" , nothing , just _listt , inj₁ _listt-bar-2 :: []) :: []
plll-start _list-seq-star-8 = (just "List-seq-7" , nothing , just _list-seq-star-8 , inj₂ ' ' :: inj₁ _list-seq-star-8 :: []) :: (just "List-seq-6" , nothing , just _list-seq-star-8 , []) :: []
plll-start _list-seq-star-7 = (just "List-seq-5" , nothing , just _list-seq-star-7 , inj₁ _list-seq-star-5 :: inj₁ _list-lit :: inj₁ _list-seq-star-6 :: inj₂ ',' :: inj₁ _list-seq-star-7 :: []) :: (just "List-seq-4" , nothing , just _list-seq-star-7 , []) :: []
plll-start _list-seq-star-6 = (just "List-seq-3" , nothing , just _list-seq-star-6 , inj₂ ' ' :: inj₁ _list-seq-star-6 :: []) :: (just "List-seq-2" , nothing , just _list-seq-star-6 , []) :: []
plll-start _list-seq-star-5 = (just "List-seq-1" , nothing , just _list-seq-star-5 , inj₂ ' ' :: inj₁ _list-seq-star-5 :: []) :: (just "List-seq-0" , nothing , just _list-seq-star-5 , []) :: []
plll-start _list-seq = (just "List-seq" , nothing , just _list-seq , inj₁ _list-seq-star-7 :: inj₁ _list-seq-star-8 :: inj₁ _list-lit :: []) :: []
plll-start _list-lit = (just "List-lit" , nothing , just _list-lit , inj₂ '[' :: inj₂ ']' :: []) :: []
plll-start _list-comma-star-4 = (just "List-comma-3" , nothing , just _list-comma-star-4 , inj₂ ' ' :: inj₁ _list-comma-star-4 :: []) :: (just "List-comma-2" , nothing , just _list-comma-star-4 , []) :: []
plll-start _list-comma-star-3 = (just "List-comma-1" , nothing , just _list-comma-star-3 , inj₂ ' ' :: inj₁ _list-comma-star-3 :: []) :: (just "List-comma-0" , nothing , just _list-comma-star-3 , []) :: []
plll-start _list-comma = (just "List-comma" , nothing , just _list-comma , inj₂ '[' :: inj₁ _list-comma-star-3 :: inj₁ _list-seq :: inj₁ _list-comma-star-4 :: inj₂ ']' :: []) :: []


plll-return : maybe gratr2-nt → 𝕃 gratr2-rule
plll-return _ = []

plll-rtn : gratr2-rtn
plll-rtn = record { start = _start ; _eq_ = gratr2-nt-eq ; gratr2-start = plll-start ; gratr2-return = plll-return }

open import run ptr
open noderiv

------------------------------------------
-- Length-decreasing rules
------------------------------------------

len-dec-rewrite : Run → maybe (Run × ℕ)
len-dec-rewrite {- List-comma-} ((Id "List-comma") :: (InputChar '[') :: (ParseTree (parsed-list-comma-star-3 x0)) :: (ParseTree (parsed-list-seq x1)) :: (ParseTree (parsed-list-comma-star-4 x2)) :: _::_(InputChar ']') rest) = just (ParseTree (parsed-list-comma (norm-list-comma (List-comma x0 x1 x2))) ::' rest , 6)
len-dec-rewrite {- List-comma-1-} ((Id "List-comma-1") :: (InputChar ' ') :: _::_(ParseTree (parsed-list-comma-star-3 x0)) rest) = just (ParseTree (parsed-list-comma-star-3 (norm-list-comma-star-3 (List-comma-1 x0))) ::' rest , 3)
len-dec-rewrite {- List-comma-3-} ((Id "List-comma-3") :: (InputChar ' ') :: _::_(ParseTree (parsed-list-comma-star-4 x0)) rest) = just (ParseTree (parsed-list-comma-star-4 (norm-list-comma-star-4 (List-comma-3 x0))) ::' rest , 3)
len-dec-rewrite {- List-lit-} ((Id "List-lit") :: (InputChar '[') :: _::_(InputChar ']') rest) = just (ParseTree (parsed-list-lit (norm-list-lit List-lit)) ::' rest , 3)
len-dec-rewrite {- List-seq-} ((Id "List-seq") :: (ParseTree (parsed-list-seq-star-7 x0)) :: (ParseTree (parsed-list-seq-star-8 x1)) :: _::_(ParseTree (parsed-list-lit x2)) rest) = just (ParseTree (parsed-list-seq (norm-list-seq (List-seq x0 x1 x2))) ::' rest , 4)
len-dec-rewrite {- List-seq-1-} ((Id "List-seq-1") :: (InputChar ' ') :: _::_(ParseTree (parsed-list-seq-star-5 x0)) rest) = just (ParseTree (parsed-list-seq-star-5 (norm-list-seq-star-5 (List-seq-1 x0))) ::' rest , 3)
len-dec-rewrite {- List-seq-3-} ((Id "List-seq-3") :: (InputChar ' ') :: _::_(ParseTree (parsed-list-seq-star-6 x0)) rest) = just (ParseTree (parsed-list-seq-star-6 (norm-list-seq-star-6 (List-seq-3 x0))) ::' rest , 3)
len-dec-rewrite {- List-seq-5-} ((Id "List-seq-5") :: (ParseTree (parsed-list-seq-star-5 x0)) :: (ParseTree (parsed-list-lit x1)) :: (ParseTree (parsed-list-seq-star-6 x2)) :: (InputChar ',') :: _::_(ParseTree (parsed-list-seq-star-7 x3)) rest) = just (ParseTree (parsed-list-seq-star-7 (norm-list-seq-star-7 (List-seq-5 x0 x1 x2 x3))) ::' rest , 6)
len-dec-rewrite {- List-seq-7-} ((Id "List-seq-7") :: (InputChar ' ') :: _::_(ParseTree (parsed-list-seq-star-8 x0)) rest) = just (ParseTree (parsed-list-seq-star-8 (norm-list-seq-star-8 (List-seq-7 x0))) ::' rest , 3)
len-dec-rewrite {- Listt-} ((Id "Listt") :: _::_(ParseTree (parsed-listt-bar-2 x0)) rest) = just (ParseTree (parsed-listt (norm-listt (Listt x0))) ::' rest , 2)
len-dec-rewrite {- Listt-0-} ((Id "Listt-0") :: _::_(ParseTree (parsed-list-comma x0)) rest) = just (ParseTree (parsed-listt-bar-2 (norm-listt-bar-2 (Listt-0 x0))) ::' rest , 2)
len-dec-rewrite {- Listt-1-} ((Id "Listt-1") :: _::_(ParseTree (parsed-list-lit x0)) rest) = just (ParseTree (parsed-listt-bar-2 (norm-listt-bar-2 (Listt-1 x0))) ::' rest , 2)
len-dec-rewrite {- Start-} ((Id "Start") :: (ParseTree (parsed-listt x0)) :: _::_(ParseTree (parsed-start-opt-1 x1)) rest) = just (ParseTree (parsed-start (norm-start (Start x0 x1))) ::' rest , 3)
len-dec-rewrite {- Start-0-} ((Id "Start-0") :: _::_(InputChar '\n') rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Start-0)) ::' rest , 2)
len-dec-rewrite {- List-comma-0-} (_::_(Id "List-comma-0") rest) = just (ParseTree (parsed-list-comma-star-3 (norm-list-comma-star-3 List-comma-0)) ::' rest , 1)
len-dec-rewrite {- List-comma-2-} (_::_(Id "List-comma-2") rest) = just (ParseTree (parsed-list-comma-star-4 (norm-list-comma-star-4 List-comma-2)) ::' rest , 1)
len-dec-rewrite {- List-seq-0-} (_::_(Id "List-seq-0") rest) = just (ParseTree (parsed-list-seq-star-5 (norm-list-seq-star-5 List-seq-0)) ::' rest , 1)
len-dec-rewrite {- List-seq-2-} (_::_(Id "List-seq-2") rest) = just (ParseTree (parsed-list-seq-star-6 (norm-list-seq-star-6 List-seq-2)) ::' rest , 1)
len-dec-rewrite {- List-seq-4-} (_::_(Id "List-seq-4") rest) = just (ParseTree (parsed-list-seq-star-7 (norm-list-seq-star-7 List-seq-4)) ::' rest , 1)
len-dec-rewrite {- List-seq-6-} (_::_(Id "List-seq-6") rest) = just (ParseTree (parsed-list-seq-star-8 (norm-list-seq-star-8 List-seq-6)) ::' rest , 1)
len-dec-rewrite {- Posinfo-} (_::_(Posinfo n) rest) = just (ParseTree (parsed-posinfo (ℕ-to-string n)) ::' rest , 1)
len-dec-rewrite {- Start-1-} (_::_(Id "Start-1") rest) = just (ParseTree (parsed-start-opt-1 (norm-start-opt-1 Start-1)) ::' rest , 1)
len-dec-rewrite x = nothing

rrs : rewriteRules
rrs = record { len-dec-rewrite = len-dec-rewrite }
