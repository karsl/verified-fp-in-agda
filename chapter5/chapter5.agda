module chapter5 where

open import nat
open import eq
open import bool
open import vector hiding (head𝕍 ; tail𝕍 ; concat𝕍 ; nth𝕍)

open import product
open import nat-nonzero hiding (suc⁺ ; _+⁺_ ; _*⁺_)

head𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → A
head𝕍 (x :: _) = x

tail𝕍 : ∀ {ℓ} {A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A (pred n)
tail𝕍 [] = []
tail𝕍 (_ :: xs) = xs

concat𝕍 : ∀{ℓ}{A : Set ℓ}{n m : ℕ} → 𝕍 (𝕍 A n) m → 𝕍 A (m * n)
concat𝕍 [] = []
concat𝕍 (x :: xs) = x ++𝕍 (concat𝕍 xs)

nth𝕍 : ∀ {ℓ} {A : Set ℓ}{m : ℕ} → (n : ℕ) → n < m ≡ tt → 𝕍 A m → A
nth𝕍 0 _ (x :: _) = x
nth𝕍 (suc n) p (_ :: xs) = nth𝕍 n p xs
nth𝕍 (suc n) () []
nth𝕍 0 () []

-- Sigma types
ℕ+ : Set
ℕ+ = Σ ℕ (λ n → iszero n ≡ ff)

suc⁺ : ℕ⁺ → ℕ⁺
suc⁺ (x , y) = (suc x , refl)

iszerosum : (a : ℕ) → (b : ℕ) → iszero a ≡ ff → iszero b ≡ ff → iszero (a + b) ≡ ff
iszerosum (suc a) (suc b) p1 p2 = refl

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
_+⁺_ (n₁ , p₁) (n₂ , p₂) = (n₁ + n₂ , iszerosum n₁ n₂ p₁ p₂)

iszeromult : ∀ (x y : ℕ) → iszero x ≡ ff → iszero y ≡ ff →
               iszero (x * y) ≡ ff
iszeromult zero zero p1 p2 = {!!}
iszeromult (suc x) (suc y) p1 p2 = refl

_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(n1 , p1) *⁺ (n2 , p2) = (n1 * n2 , {!!})


-- For testing --------------------------------------------------------------------
exampleVector : 𝕍 ℕ 5
exampleVector = (1 :: (2 :: (3 :: (4 :: (5 :: [])))))
