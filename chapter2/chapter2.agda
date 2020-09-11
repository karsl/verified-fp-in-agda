module chapter2 where

open import bool
open import eq

-- Exercise 1
&&-combo : {p1 p2 : 𝔹} → p1 ≡ tt → p2 ≡ tt → p1 && p2 ≡ tt
&&-combo {tt} proof1 proof2 = proof2
&&-combo {ff} ()

-- Assume p1 = true then the the formula becomes tt ≡ tt → p2 ≡ tt → tt && p2 ≡ tt
-- ⇔ p2 ≡ tt → p2 ≡ tt
--
-- When p1 = false then the formula becomes ff ≡ ff → ... which has an unsatisfiable assumptions.

-- Exercise 2
distrib : ∀ {b1 b2 b3} → (b1 && b2) || b3 ≡ (b1 || b3) && (b2 || b3)
distrib {tt} {tt} {tt} = refl
distrib {tt} {tt} {ff} = refl
distrib {tt} {ff} {tt} = refl
distrib {tt} {ff} {ff} = refl
distrib {ff} {tt} {tt} = refl
distrib {ff} {tt} {ff} = refl
distrib {ff} {ff} {tt} = refl
distrib {ff} {ff} {ff} = refl

another : ∀ {b1 b2} → b1 ≡ tt → b1 && b2 ≡ b2
another {tt} p = refl
another {ff} ()

another' : ∀ {b1 b2} → b1 ≡ tt → b1 && b2 ≡ b2
another' p rewrite p = refl


-- Exercises 3
a : tt ≡ tt
a = refl

b : ff ≡ ff
b = refl

d : ff && ff ≡ ~ tt
d = refl

e : {x : 𝔹} → tt && x ≡ x
e = refl

-- f : {x : 𝔹} → x && tt ≡ x
-- f = refl
