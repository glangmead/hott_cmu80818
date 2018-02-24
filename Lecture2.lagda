\begin{code}
module Lecture2 where

Type = Set

data ℕ : Type where
  Nzero : ℕ
  Nsucc : ℕ → ℕ

-- induction: for any dependent type P over ℕ, define a section of P
-- built out of a term in P 0 and a section of P n → P(Nsucc n)
ind-N : {P : ℕ → Type} → P Nzero → ((n : ℕ) → P n → P(Nsucc n)) → ((n : ℕ) → P n)
ind-N p0 pS Nzero = p0
ind-N p0 pS (Nsucc n) = pS n (ind-N p0 pS n)

-- use the general induction principle to define addition
-- in this case P is ℕ, the special non-dependent type over ℕ, and
-- so sections of P (dependent functions Π_{x:ℕ} P(x)) are functions ℕ → ℕ
add0 : ℕ → ℕ
add0 n = n
addS : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
addS n f m = Nsucc (f m)
add : ℕ → ℕ → ℕ
add = ind-N add0 addS

_+_ : ℕ → ℕ → ℕ
n + m = add n m

_**_ : ℕ → (ℕ → ℕ)
Nzero ** n = Nzero
(Nsucc m) ** n = (m ** n) + n

_^_ : ℕ → (ℕ → ℕ)
m ^ Nzero = Nsucc Nzero
m ^ (Nsucc n) = m ** (m ^ n)

factorial : ℕ → ℕ
factorial Nzero = Nsucc Nzero
factorial (Nsucc m) = (Nsucc m) ** (factorial m)

Nmax : ℕ → (ℕ → ℕ)
Nmax Nzero n = n
Nmax (Nsucc m) Nzero = Nsucc m
Nmax (Nsucc m) (Nsucc n) = Nsucc (Nmax m n)

Nmin : ℕ → (ℕ → ℕ)
Nmin Nzero n = Nzero
Nmin (Nsucc m) Nzero = Nzero
Nmin (Nsucc m) (Nsucc n) = Nsucc (Nmin m n)
\end{code}
