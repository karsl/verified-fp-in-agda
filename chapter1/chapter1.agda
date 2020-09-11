module chapter1 where

data 𝔹 : Set where
  ff : 𝔹
  tt : 𝔹

infix 7 ~_
infixl 6 _xor_ _nand_
infixr 6 _&&_
infixr 5 _||_

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

if_then_else : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then a else b = a
if ff then a else b = b

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor tt = ff
ff xor ff = ff
x xor y = tt

_nand_ : 𝔹 → 𝔹 → 𝔹
x nand y = ~ (x && y)

data day : Set where
  monday : day
  tuesday : day
  wednesday : day
  thursday : day
  friday : day
  saturday : day
  sunday : day

nextday : day → day
nextday monday = tuesday
nextday tuesday = wednesday
nextday wednesday = thursday
nextday thursday = friday
nextday friday = saturday
nextday saturday = sunday
nextday sunday = monday

data suit : Set where
  hearts : suit
  spades : suit
  diamonds : suit
  clubs : suit

is-red : suit → 𝔹
is-red hearts = tt
is-red diamonds = tt
is-red spades = ff
is-red clubs = ff
