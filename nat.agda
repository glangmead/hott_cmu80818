module INTRO where

data ℕ : Set where
  Nzero : ℕ
  Nsucc : ℕ → ℕ

_+_ : ℕ → (ℕ → ℕ)
  Nzero + n = n
  (Nsucc m) + m = Nsucc (n + m)

_*_ : ℕ → (ℕ → ℕ)
  Nzero * n = Nzero
  (Nsucc m) * n = (m * n) + n

_^_ : ℕ → (ℕ → ℕ)
  m ^ Nzero = Nsucc Nzero
  m ^ (Nsucc n) = m * (m ^ n)

factorial : ℕ → ℕ
  factorial Nzero = Nsucc Nzero
  factorial (Nsucc m) = (Nsucc m) * (factorial m)

Nmax : ℕ → (ℕ → ℕ)
  Nmax Nzero n = n
  Nmax (Nsucc m) Nzero = Nsucc m
  Nmax (Nsucc m) (Nsucc n) = Nsucc (Nmax m n)

Nmin : ℕ → (ℕ → ℕ)
  Nmin Nzero n = Nzero
  Nmin (Nsucc m) Nzero = Nzero
  Nmin (Nsucc m) (Nsucc n) = Nsucc (Nmin m n)

