module chapter3 where

open import eq
open import bool

open import nat hiding (iszero)

-- Addition ---------------------------------------------------------------------

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x ) y rewrite +suc y x | +comm x y = refl

-- Multiplication --------------------------------------------------------------------

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y = {!!}

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *assoc x y z | *distribr y (x * y) z = refl

-- Comparison --------------------------------------------------------------------

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 zero = refl
<-0 (suc x) = refl

𝔹-contra : ff ≡ tt → ∀ {P : Set} → P
𝔹-contra ()

<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {y = 0} p1 p2 rewrite <-0 x = 𝔹-contra p1
<-trans {0} {suc y} {0} p1 ()
<-trans {0} {suc y} {suc z} p1 p2 = refl
<-trans {suc x} {suc y} {0} p1 ()
<-trans {suc x} {suc y} {suc z} p1 p2 rewrite <-trans {x} {y} {z} p1 p2 = refl

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl 0 = refl
=ℕ-refl (suc x) = =ℕ-refl x

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {0} {0} u = refl
=ℕ-to-≡ {suc x} {0} ()
=ℕ-to-≡ {0} {suc y} ()
=ℕ-to-≡ {suc x} {suc y} p rewrite =ℕ-to-≡ {x} {y} p = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from-≡ {x} refl =  =ℕ-refl x

-- Exercises --------------------------------------------------------------------

-- Exercise 1
iszero : ℕ → 𝔹
iszero 0 = tt
iszero (suc x) = ff

nonzero< : ∀ {n : ℕ} → iszero n ≡ ff → 0 < n ≡ tt
nonzero< {0} ()
nonzero< {suc n} p = refl

iszerosum : ∀ (x y : ℕ) → iszero(x + y) ≡ iszero(x) && iszero(y)
iszerosum zero y = refl
iszerosum (suc x) y = refl

iszerosum2 : ∀ (x y : ℕ) → iszero x ≡ ff → iszero(x + y) ≡ ff
iszerosum2 zero y ()
iszerosum2 (suc x) y p = refl

<-not-> : ∀{x y : ℕ} → x < y ≡ tt → y < x ≡ ff
<-not-> {zero} {suc y} p = refl
<-not-> {suc x} {suc y} p = <-not-> {x} {y} p

-- Exercise 2
>-trans : ∀ {x y z : ℕ} → x > y ≡ tt → y > z ≡ tt → x > z ≡ tt
>-trans {suc x} {suc y} {zero} p1 p2 = refl
>-trans {suc x} {suc y} {suc z} p1 p2 = >-trans {x} {y} {z} p1 p2

<-trans' : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans' {zero} {suc y} {suc z} p1 p2 = refl
<-trans' {suc x} {suc y} {suc z} p1 p2 = <-trans' p1 p2

<+ : ∀ {x y : ℕ} → y =ℕ 0 ≡ ff → x < (y + x) ≡ tt
<+ {y = 0} ()
<+ {zero} {suc y} p = refl
<+ {suc x} {suc y} p = {!!}

-- Exercise 3
{-
a) (iv)
b) (i)
-}
