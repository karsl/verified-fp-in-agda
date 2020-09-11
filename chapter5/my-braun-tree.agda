open import nat
open import bool
open import eq
open import sum
open import nat-thms
open import product
open import sum

module my-braun-tree {ℓ} (A : Set ℓ) (_<A_ : A → A → 𝔹) where

data braun-tree : (n : ℕ) → Set ℓ where
  bt-empty : braun-tree 0
  bt-node : ∀ {n m : ℕ} →
            A → braun-tree n → braun-tree m →
            n ≡ m ∨ n ≡ suc m →
            braun-tree (suc (n + m))


bt-insert : ∀ {n : ℕ} → A → braun-tree n → braun-tree (suc n)
bt-insert v bt-empty = bt-node v bt-empty bt-empty (inj₁ refl)


bt-insert a (bt-node{n}{m} a' l r p) rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
bt-insert a (bt-node{n}{m} a' l r _) | inj₁ p | (a1 , a2) rewrite p = bt-node a1 (bt-insert a2 r) l (inj₂ refl)
bt-insert a (bt-node{n}{m} a' l r _) | inj₂ p | (a1 , a2) rewrite p = bt-node a2 (bt-insert a1 r) l (inj₁ refl)

bt-delete-min : ∀ {p : ℕ} → braun-tree (suc p) → braun-tree p
bt-delete-min = {!!}

bt-remove-min : ∀ {p : ℕ} → braun-tree (suc p) → A × braun-tree p
bt-remove-min (bt-node a l r u) = a , bt-delete-min (bt-node a l r u)

bt-replace-min : ∀{n : ℕ} → A → braun-tree (suc n) → braun-tree (suc n)
bt-replace-min a (bt-node _ bt-empty bt-empty u) = (bt-node a bt-empty bt-empty u)
bt-replace-min a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₁ ()))
bt-replace-min a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₂ ()))
bt-replace-min a (bt-node _ (bt-node _ _ _ _) bt-empty (inj₁ ()))
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) with a <A x
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | tt = (bt-node a (bt-node x l r u) bt-empty (inj₂ y))
bt-replace-min a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | ff =
 (bt-node x (bt-replace-min a (bt-node x l r u)) bt-empty (inj₂ y))
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) with a <A x && a <A x'
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | tt =
 (bt-node a (bt-node x l r u) (bt-node x' l' r' u') v)
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff with x <A x'
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | tt =
 (bt-node x (bt-replace-min a (bt-node x l r u)) (bt-node x' l' r' u') v)
bt-replace-min a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | ff =
 (bt-node x' (bt-node x l r u) (bt-replace-min a (bt-node x' l' r' u')) v)
