\begin{code}
module Lecture3 where

import Lecture2
open Lecture2

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

reflexive-EqN : (n : ℕ) → EqN n n
reflexive-EqN Nzero = star
reflexive-EqN (Nsucc n) = reflexive-EqN n

symmetric-EqN : (m n : ℕ) → EqN m n → EqN n m
symmetric-EqN Nzero Nzero t = t
symmetric-EqN Nzero (Nsucc n) t = t
symmetric-EqN (Nsucc n) Nzero t = t
symmetric-EqN (Nsucc m) (Nsucc n) t = symmetric-EqN m n t

{-
transitive-EqN : (l m n : ℕ) → EqN l m → EqN m n → EqN l n
transitive-EqN Nzero Nzero Nzero s t = star
transitive-EqN (Nsucc l) (Nsucc m) (Nsucc n) s t = transitive-EqN l m n s t
-}
\end{code}
