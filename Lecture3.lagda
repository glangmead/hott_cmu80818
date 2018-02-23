module Lecture3 where

import Lecture2

data unit : Set where
  star : unit

data empty : Set where

¬ : Set → Set
  ¬ A = A → empty

data coprod (A : Set) (B : Set) : Set where
  inl : A → coprod A B
  inr : B → coprod A B

data Sigma (A : Set) (B : A → Set) : Set where
  dpair : (x : A) → (B x → Sigma A B)

data prod (A : Set) (B : Set) : Set where
  pair : A → (B → prod A B)

EqN : ℕ → (ℕ → Set)
  EqN Nzero Nzero = unit
  EqN Nzero (Nsucc n) = empty
  EqN (Nsucc m) Nzero = empty
  EqN (Nsucc m) (Nsucc n) = EqN m n

reflexive_EqN : (n : ℕ) → EqN n n
  reflexive_EqN Nzero = star
  reflexive_EqN (Nsucc n) = reflexive_EqN n

symmetric_EqN : (m n : ℕ) → EqN m n → EqN n m
  symmetric_EqN Nzero Nzero t = t
  symmetric_EqN (Nsucc m) (Nsucc n) t = symmetric_EqN m n t

transitive_EqN : (l m n : ℕ) → EqN l m → EqN m n → EqN l n
  transitive_EqN Nzero Nzero Nzero s t = star
  transitive_EqN (Nsucc l) (Nsucc m) (Nsucc n) s t = transitive_EqN l m n s t
