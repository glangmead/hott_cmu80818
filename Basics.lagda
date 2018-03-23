\begin{code}

{-# OPTIONS --without-K #-}

module Basics where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : (i : Level) → Set (lsuc i)
UU i = Set i


U = UU lzero
Type = UU (lsuc lzero)

Π : {i j : Level} {A : UU i} → (P : A → UU j) → UU (i ⊔ j)
Π {_} {_} {A} P = (a : A) → P a

\end{code}
