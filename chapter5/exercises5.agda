open import vector
open import nat
open import eq
open import bool
open import nat-thms
open import product

open import bool-relations using (transitive ; total)

module exercises5
       (A : Set)
       (_≤A_ : A → A → 𝔹)
       (≤A-trans : transitive _≤A_)
       (≤A-total : total _≤A_)
       where

open import bool-relations _≤A_ hiding (transitive ; total)
open import minmax _≤A_ ≤A-trans ≤A-total
open import bst A _≤A_ ≤A-trans ≤A-total using (bst)

-- Exercise 1
_by_matrix : (n : ℕ) → (m : ℕ) → Set
n by m matrix = 𝕍 (𝕍 ℕ m) n

-- Exercise 2
-- a)
zeros : (n : ℕ) → 𝕍 ℕ n
zeros 0 = []
zeros (suc n) = 0 :: zeros n

zero-matrix : (n : ℕ) → (m : ℕ) → n by m matrix
zero-matrix zero _ = []
zero-matrix (suc n) m = (zeros m) :: zero-matrix n m

-- b)
matrix-elt : ∀ {n m : ℕ} → n by m matrix → (i : ℕ) → (j : ℕ) → i < n ≡ tt → j < m ≡ tt → ℕ
matrix-elt mat i j p₁ p₂ = nth𝕍 j p₂ (nth𝕍 i p₁ mat)

-- c)
update-element-at : ∀ {ℓ} {n : ℕ} {A : Set ℓ} → 𝕍 A n → (a : A) → (i : ℕ) → i < n ≡ tt → 𝕍 A n
update-element-at (x :: xs) a 0 p = a :: xs
update-element-at (x :: xs) a (suc i) p = x :: update-element-at xs a i p

value-vector : (n : ℕ) → (i : ℕ) → ℕ → i < n ≡ tt → 𝕍 ℕ n
value-vector n i e p = update-element-at (zeros n) e i p

update-element-at-matrix : ∀ {n m : ℕ} → n by m matrix → ℕ → (i : ℕ) → (j : ℕ)
                           → i < n ≡ tt → j < m ≡ tt → n by m matrix
update-element-at-matrix (x :: xs) a (suc i) j p₁ p₂ = x :: update-element-at-matrix xs a i j p₁ p₂
update-element-at-matrix (x :: xs) a 0 j _ p₂ = update-element-at x a j p₂ :: xs

suc-less : (i : ℕ) → (n : ℕ) → suc i < n ≡ tt → i < n ≡ tt
suc-less zero (suc n) _ = refl
suc-less (suc i) (suc n) p rewrite suc-less i n p = refl

diagonal-matrix : (n : ℕ) → (i : ℕ) → ℕ → i < n ≡ tt → i by n matrix
diagonal-matrix n 0 e p = []
diagonal-matrix n (suc i) e p = value-vector n (suc i) e p :: diagonal-matrix n i e (suc-less i n p)

-- d)
transpose : ∀ {n m : ℕ} → n by m matrix → m by n matrix
transpose{m = 0} mat = []
transpose{0}{suc m} mat = [] :: transpose{0}{m} []
transpose{suc n}{suc m} mat = (map𝕍 head𝕍 mat) :: transpose{suc n}{m} (map𝕍 tail𝕍 mat)

-- e)
_•_ : ∀ {n : ℕ} → 𝕍 ℕ n → 𝕍 ℕ n → ℕ
[] • [] = 0
(x :: xs) • (y :: ys) = x * y + (xs • ys)

-- f)
_•matrix_ : ∀ {n m : ℕ} → 𝕍 ℕ n → m by n matrix → 𝕍 ℕ m
vec •matrix [] = []
vec •matrix (x :: xs) = vec • x :: vec •matrix xs

_*matrix_ : ∀ {n k m : ℕ} → n by k matrix → k by m matrix → n by m matrix
[] *matrix mat2 = []
(x :: xs) *matrix mat2 = (x •matrix transpose mat2) :: xs *matrix mat2

--  3)
again𝕍 : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (v : 𝕍 A n) → 𝕃-to-𝕍 (𝕍-to-𝕃 v) ≡ (n , v)
again𝕍 [] = refl
again𝕍 (x :: xs) rewrite again𝕍 xs = refl

-- 4)
unzip𝕍 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {n : ℕ} → 𝕍 (A × B) n → (𝕍 A n × 𝕍 B n)
unzip𝕍 [] = [] , []
unzip𝕍 (x :: xs) = fst x :: fst (unzip𝕍 xs) , snd x :: snd (unzip𝕍 xs)

-- 5)
remove-min : ∀ {l u : A} → bst l u → bst l u
remove-min (bst.bst-leaf p) = bst.bst-leaf p
remove-min (bst.bst-node d (bst.bst-leaf p1) (bst.bst-leaf p2) p3 p4)
  = bst.bst-leaf (≤A-trans (≤A-trans p3 (≤A-trans p1 p2)) p4)
remove-min (bst.bst-node d (bst.bst-leaf p1) (bst.bst-node d1 l1 r1 p5 p6) p3 p4)
  = bst.bst-node d1 l1 r1 (≤A-trans p3 (≤A-trans p1 p5)) (≤A-trans (≤A-trans ≤A-refl p6) p4)
remove-min (bst.bst-node d ll@(bst.bst-node d' L' R' p1 p2) R p3 p4) = bst.bst-node d (remove-min ll) R p3 p4

-- remove-max : ∀ {l u : A} → bst l u → bst l u
-- remove-max t = {!!}

--6)
--TODO

-- Test
v1 : 𝕍 ℕ 2
v1 = 1 :: 2 :: []

v2 : 𝕍 ℕ 2
v2 = 3 :: 4 :: []

v3 : 𝕍 ℕ 2
v3 = 5 :: 6 :: []

v4 : 𝕍 ℕ 3
v4 = 7 :: 8 :: 9 :: []

m1 : 3 by 2 matrix
m1 = v1 :: v2 :: v3 :: []

m2 : 2 by 3 matrix
m2 = transpose m1

m3 : 3 by 3 matrix
m3 = (v1 :: v3 :: v2 :: []) *matrix (v4 :: v4 :: [])
