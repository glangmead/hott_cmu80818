\begin{code}

{-# OPTIONS --without-K #-}

module Lecture6 where

import Lecture5
open Lecture5 public

is-contr : {i : Level} → UU i → UU i
is-contr A = Sigma A (λ a → (x : A) → Id a x)

center : {i : Level} {A : UU i} → is-contr A → A
center (dpair c C) = c

-- We make sure that the contraction is coherent in a straightforward way
contraction : {i : Level} {A : UU i} (H : is-contr A) → (const A A (center H) ~ id)
contraction (dpair c C) x = concat _ (inv (C c)) (C x)

coh-contraction : {i : Level} {A : UU i} (H : is-contr A) →
  Id (contraction H (center H)) refl
coh-contraction (dpair c C) = left-inv (C c)

ev-pt : {i j : Level} (A : UU i) (a : A) (B : A → UU j) → ((x : A) → B x) → B a
ev-pt A a B f = f a

sing-ind-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) → B (center H) → (x : A) → B x
sing-ind-is-contr A H B b x = tr B (contraction H x) b

sing-comp-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) → (((ev-pt A (center H) B) ∘ (sing-ind-is-contr A H B)) ~ id)
sing-comp-is-contr A H B b = ap (λ (ω : Id (center H) (center H)) → tr B ω b) (coh-contraction H)

is-sing-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) → sec (ev-pt A (center H) B)
is-sing-is-contr A H B = dpair (sing-ind-is-contr A H B) (sing-comp-is-contr A H B)

is-sing : {i : Level} (A : UU i) → A → UU (lsuc i)
is-sing {i} A a = (B : A → UU i) → sec (ev-pt A a B)

is-contr-is-sing : {i : Level} (A : UU i) (a : A) → is-sing A a → is-contr A
is-contr-is-sing A a S = dpair a (pr1 (S (λ y → Id a y)) refl)

\end{code}
