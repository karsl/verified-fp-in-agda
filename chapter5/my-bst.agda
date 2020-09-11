open import bool
open import eq
open import maybe
open import product
open import product-thms
open import bool-relations using (transitive ; total)

module my-bst
  (A : Set) (_≤A_ : A → A → 𝔹)
  (≤A-trans : transitive _≤A_)
  (≤A-total : total _≤A_) where

open import minmax _≤A_ ≤A-trans ≤A-total
open import bool-relations _≤A_ hiding (transitive ; total)

data bst : A → A → Set where
  bst-leaf : ∀ {l u : A} → l ≤A u ≡ tt → bst l u
  bst-node : ∀ {l l' u' u : A}(d : A) →
               bst l' d → bst d u' →
               l ≤A l' ≡ tt → u' ≤A u ≡ tt →
               bst l u

bst-search : ∀{l u : A} → (d : A) → bst l u → maybe (Σ A (λ d' → d iso𝔹 d' ≡ tt))
bst-search d (bst-leaf p) = nothing
bst-search d (bst-node d' l r p1 p2) with keep (d ≤A d')
bst-search d (bst-node d' l r p1 p2) | tt , p with keep (d' ≤A d)
bst-search d (bst-node d' l r p1 p2) | tt , p | tt , p3 = just (d' , iso𝔹-intro p p3)
bst-search d (bst-node d' l r p1 p2) | tt , p | ff , p3 = bst-search d l
bst-search d (bst-node d' l r p1 p2) | ff , p = bst-search d r

bst-insert : ∀ {l u : A} → (d : A) → bst l u → bst (min d l) (max d u)
bst-insert d (bst-leaf p) = bst-node d (bst-leaf ≤A-refl) (bst-leaf ≤A-refl) min-≤1 max-≤1
bst-insert d (bst-node d' l r p1 p2) with keep (d ≤A d')
bst-insert d (bst-node d' l r p1 p2) | tt , p3 with keep (d' ≤A d)
bst-insert d (bst-node d' l r p1 p2) | tt , p3 | tt , p4 = {!!}
bst-insert d (bst-node d' l r p1 p2) | tt , p3 | ff , p4 = {!!}
bst-insert d (bst-node d' l r p1 p2) | ff , p3 = {!!}
