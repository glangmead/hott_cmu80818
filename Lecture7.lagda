\begin{code}

{-# OPTIONS --without-K #-}

module Lecture7 where

import Lecture6
open Lecture6 public

-- Section 7.1 Fiberwise equivalences
tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ({x : A} → B x → C x) → ( Σ A B → Σ A C)
tot f (dpair x y) = dpair x (f y)

\end{code}
