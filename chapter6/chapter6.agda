module chapter6 where

open import integer
open import nat
open import bool
open import eq
open import unit
open import nat-thms
open import string
open import string-format
open import list-simplifier
open import list
open import list-thms

-- Exercise 1
negate : ℤ → ℤ
negate (mkℤ 0 t) = mkℤ 0 t
negate (mkℤ (suc n) b) = mkℤ (suc n) (~ b)

_-ℤ_ : ℤ → ℤ → ℤ
x -ℤ y = x +ℤ (negate y)

_*ℤ_ : ℤ → ℤ → ℤ
mkℤ zero s1 *ℤ _ = mkℤ zero s1
mkℤ (suc n1) s1 *ℤ mkℤ zero s2 = mkℤ zero s2
mkℤ (suc n1) s1 *ℤ mkℤ (suc n2) s2 = mkℤ ((suc n1) * (suc n2)) (s1 xor s2)

-- Exercise 2
+ℤ-comm : ∀ {z1 z2 : ℤ} → z1 +ℤ z2 ≡ z2 +ℤ z1
+ℤ-comm {mkℤ zero triv} {mkℤ zero triv} = refl
+ℤ-comm {mkℤ zero triv} {mkℤ (suc n2) s2} = refl
+ℤ-comm {mkℤ (suc n1) s1} {mkℤ zero s2} = refl
+ℤ-comm {mkℤ (suc n1) tt} {mkℤ (suc n2) tt} rewrite +comm n1 (suc n2) | +comm n2 (suc n1) | +comm n1 n2 = refl
+ℤ-comm {mkℤ (suc n1) tt} {mkℤ (suc n2) ff} = refl
+ℤ-comm {mkℤ (suc n1) ff} {mkℤ (suc n2) tt} = refl
+ℤ-comm {mkℤ (suc n1) ff} {mkℤ (suc n2) ff} rewrite +comm n1 (suc n2) | +comm n2 (suc n1) | +comm n1 n2 = refl

-- Exercise 3
format-my-test : string
format-my-test = format "%%n%n%" 1 100

format-my-test2 : string
format-my-test2 = format "%%s%%n%" "1" 100

-- Exercise 4
-- -- TODO This shouldn't have been working for 0. Problem is, it doesn't do any simplication.
-- -- It actually just converts the representations to the actual form and does everything what it does within that form.
-- map-append-simp : ∀ {A B : Set} (f : A → B) (l1 l2 : 𝕃 A)
--                   → 𝕃⟦ 𝕃ʳ-simp ((map f (l1 ++ l2)) ʳ) 0 ⟧ ≡ 𝕃⟦ mapʳ f ((l1) ʳ) ++ʳ mapʳ f (l2 ʳ) ⟧
-- map-append-simp f [] l2 = refl
-- map-append-simp f (x :: l1) l2 rewrite map-append-simp f l1 l2 = refl

map-append-simp : ∀ {A B : Set} (f : A → B) (l1 l2 : 𝕃 A)
                  → 𝕃ʳ-simp ((map f (l1 ++ l2))ʳ) 3 ≡ ((map f l1 ++ map f l2) ʳ)
map-append-simp f l1 l2 = {!!}

test-list : ∀ {A B : Set} → (f : A → B) → (l1 l2 : 𝕃 A) → 𝕃ʳ B
test-list f l1 l2 = ((map f l1) ++ (map f l2))ʳ

test-simp : ∀ {A B : Set} → (f : A → B) → (l1 l2 : 𝕃 A) → 𝕃ʳ B
test-simp f l1 l2 = 𝕃ʳ-simp (test-list f l1 l2) 10
