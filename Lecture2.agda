{-# OPTIONS --without-K #-}

module Lecture2 where

import Basics
open Basics public

-- Definition 2.2.3 define the identity function, and show lambda-abstraction in so doing
id : {i : Level} {A : UU i} → A → A
id = λ a → a -- can also use plain backslash \ instead of lambda (as it resembles lambda?)

-- Definition 2.2.4
comp : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → ((A → B) → (A → C))
comp = λ g f a → g(f(a)) -- the lambda extends to cover g, f and a
_∘_ : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → ((A → B) → (A → C))
g ∘ f = comp g f

data ℕ : U where
  Nzero : ℕ
  Nsucc : ℕ → ℕ

add : ℕ → ℕ → ℕ
add Nzero = id
add (Nsucc n) = Nsucc ∘ (add n)

-- try some examples, hit C-c C-n (or whatever "compute normal form" is bound to)
-- and try entering "add (Nsucc Nzero) (Nsucc (Nsucc Nzero))"
-- you should get "Nsucc (Nsucc (Nsucc Nzero))"

_+_ : ℕ → ℕ → ℕ
n + m = add n m

-- Exercise 2.3
const : {i j : Level} (A : UU i) (B : UU j) (b : B) → A → B
const A B b x = b

-- Exercise 2.4
Pi-swap : {i j k : Level} {A : UU i} {B : UU j} {C : A → (B → UU k)} →
  ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
Pi-swap f y x = f x y

-- Exercise 2.5(a)
_**_ : ℕ → (ℕ → ℕ)
Nzero ** n = Nzero
(Nsucc m) ** n = (m ** n) + n

-- Exercise 2.5(b)
_^_ : ℕ → (ℕ → ℕ)
m ^ Nzero = Nsucc Nzero
m ^ (Nsucc n) = m ** (m ^ n)

-- Exercise 2.5(c)
factorial : ℕ → ℕ
factorial Nzero = Nsucc Nzero
factorial (Nsucc m) = (Nsucc m) ** (factorial m)

-- Exercise 2.6(a)
Nmax : ℕ → (ℕ → ℕ)
Nmax Nzero n = n
Nmax (Nsucc m) Nzero = Nsucc m
Nmax (Nsucc m) (Nsucc n) = Nsucc (Nmax m n)

-- Exercise 2.6(b)
Nmin : ℕ → (ℕ → ℕ)
Nmin Nzero n = Nzero
Nmin (Nsucc m) Nzero = Nzero
Nmin (Nsucc m) (Nsucc n) = Nsucc (Nmin m n)

-- Exercise 2.7
-- induction: for any dependent type P over ℕ, define a section of P
-- built out of a term in P 0 and a section of P n → P(Nsucc n)
ind-N : {i : Level} {P : ℕ → UU i} → P Nzero → ((n : ℕ) → P n → P(Nsucc n)) → ((n : ℕ) → P n)
ind-N p0 pS Nzero = p0
ind-N p0 pS (Nsucc n) = pS n (ind-N p0 pS n)
