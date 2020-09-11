module chapter4 where

open import bool
open import nat
open import eq
open import nat-thms
open import product
open import product-thms
open import list hiding (length ; _++_ ; map ; filter ; reverse-helper; reverse ; repeat ; nthTail)

-- Lists Part
length : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x :: xs) = f x :: map f xs

filter : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in
                     if p x then x :: r else r

reverse-helper : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
reverse-helper h [] = h
reverse-helper h (x :: xs) = reverse-helper (x :: h) xs

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = reverse-helper [] l

-- Reasoning about part
length-++ : ∀ {ℓ} {A : Set ℓ} (l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (x :: l1) l2 rewrite length-++ l1 l2 = refl

++-assoc : ∀ {ℓ} {A : Set ℓ} (l1 l2 l3 : 𝕃 A) → (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: l1) l2 l3 rewrite ++-assoc l1 l2 l3 = refl

length-filter : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
                length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x :: xs) with p x
length-filter p (x :: xs) | tt = length-filter p xs
-- length (filter p xs) ≤ suc (length xs)
length-filter p (x :: xs) | ff =
  ≤-trans{length (filter p xs)} (length-filter p xs) (≤-suc (length xs))

filter-idem : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
              (filter p (filter p l)) ≡ (filter p l)
filter-idem p [] = refl
filter-idem p (x :: l) with keep (p x)
filter-idem p (x :: l) | tt , p' rewrite p' | p' | filter-idem p l = refl
filter-idem p (x :: l) | ff , p' rewrite p' = filter-idem p l

length-reverse-helper : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) →
                      length (reverse-helper h l) ≡ length h + length l
length-reverse-helper h [] rewrite +0 (length h) = refl
length-reverse-helper h (x :: xs)
  rewrite length-reverse-helper (x :: h) xs | +suc (length h) (length xs) = refl

length-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
length-reverse l rewrite length-reverse-helper [] l = refl

-- Exercises

-- Exercise 1
{-
a is.

b isn't. It says map increases the length of the list by 1 which isn't true.

c is. We have bunch of 'a's and then we apply p to each a which returns ff for each a.
As none of them returns true, they can't pass through the filter and the results is empty set
(This is also the case when n = 0).


d isn't. if l is empty so is it's reverse. Alternatively, reverse functions doesn't add any
item to the list so if the original list's size is n (n = 0 in our problem),
it's reverse is also n.

e is.
-}

-- Exercise 2
{-
a) (i), (iii), (iv), (v)
(ii) is missing the type of inner list.

b) (i), (iii)
(ii) is missing the definition for A.
(iv)'s return type is not a type but a value.

c) (i), (ii)
(iii) has type error for the types of f and g.
(iv) has less parameters.
(v) A's type confuses me and also Agda complains about it.
-}

test : ∀ {B : Set}{A : 𝕃 B} → (A → B) → (B → B) → 𝕃 A → 𝕃 B
test f g x = map g (map f x)


-- Exercise 3
takeWhile : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
takeWhile p [] = []
takeWhile p (x :: xs) with p x
takeWhile p (x :: xs) | tt = x :: takeWhile p xs
takeWhile p (x :: xs) | ff = []


-- Exercise 4
repeat : ∀{ℓ}{A : Set ℓ} → ℕ → A → 𝕃 A
repeat 0 a = []
repeat (suc n) a = a :: (repeat n a)

exercise4 : ∀{ℓ}{A : Set ℓ}{a : A}{p : A → 𝔹}{n : ℕ} → (p a ≡ tt) → takeWhile p (repeat n a) ≡ repeat n a
exercise4 {n = 0} pr = refl
exercise4 {p = p₁}{n = suc x} pr rewrite pr | exercise4{p = p₁}{n = x} pr = refl

-- Exercise 5
take : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
take _ [] = []
take 0 (x :: xs) = []
take (suc n') (x :: xs) = x :: take n' xs

-- Exercise 6
nthTail : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
nthTail 0 l = l
nthTail n [] = []
nthTail (suc n) (x :: l) = nthTail n l

take-nthTail : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → (n : ℕ) → l ≡ take n l ++ nthTail n l
take-nthTail [] zero = refl
take-nthTail [] (suc l) = refl
take-nthTail (x :: xs) zero = refl
take-nthTail (x :: xs) (suc n') rewrite sym (take-nthTail xs n') = refl

-- For tests
predicate : ℕ → 𝔹
predicate x = x ≤ 3

exampleList : 𝕃 ℕ
exampleList = (1 :: (2 :: (3 :: (4 :: (5 :: [])))))

tw : 𝕃 ℕ
tw = takeWhile predicate exampleList

t1 : 𝕃 ℕ
t1 = take 30 []
