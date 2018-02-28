\begin{code}
module Lecture3 where

import Lecture2
open Lecture2

data unit : Type where
  star : unit
𝟙 = unit
ind-unit : {P : unit → Type} → P star → ((x : unit) → P x)
ind-unit p star = p

data empty : Type where
𝟘 = empty
ind-empty : {P : empty → Type} → ((x : empty) → P x)
ind-empty ()

¬ : Type → Type
¬ A = A → empty

data coprod (A : Type) (B : Type) : Type where
  inl : A → coprod A B
  inr : B → coprod A B

data Sigma (A : Type) (B : A → Type) : Type where
  dpair : (x : A) → (B x → Sigma A B)

data prod (A : Type) (B : Type) : Type where
  pair : A → (B → prod A B)

EqN : ℕ → (ℕ → Type)
EqN Nzero Nzero = 𝟙
EqN Nzero (Nsucc n) = 𝟘
EqN (Nsucc m) Nzero = 𝟘
EqN (Nsucc m) (Nsucc n) = EqN m n

reflexive-EqN : (n : ℕ) → EqN n n
reflexive-EqN Nzero = star
reflexive-EqN (Nsucc n) = reflexive-EqN n

symmetric-EqN : (m n : ℕ) → EqN m n → EqN n m
symmetric-EqN Nzero Nzero t = t
symmetric-EqN Nzero (Nsucc n) t = t
symmetric-EqN (Nsucc n) Nzero t = t
symmetric-EqN (Nsucc m) (Nsucc n) t = symmetric-EqN m n t

transitive-EqN : (l m n : ℕ) → EqN l m → EqN m n → EqN l n
transitive-EqN Nzero Nzero Nzero s t = star
transitive-EqN (Nsucc n) Nzero Nzero s t = ind-empty s
transitive-EqN Nzero (Nsucc n) Nzero s t = ind-empty s
transitive-EqN Nzero Nzero (Nsucc n) s t = ind-empty t
transitive-EqN (Nsucc l) (Nsucc m) Nzero s t = ind-empty t
transitive-EqN (Nsucc l) Nzero (Nsucc n) s t = ind-empty s
transitive-EqN Nzero (Nsucc m) (Nsucc n) s t = ind-empty s
transitive-EqN (Nsucc l) (Nsucc m) (Nsucc n) s t = transitive-EqN l m n s t

\end{code}
