\begin{code}

{-# OPTIONS --without-K #-}

module Lecture8 where

import Lecture7
open Lecture7 public

-- Section 8.1 Propositions

is-prop : {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

is-prop-empty : is-prop empty
is-prop-empty ()

is-prop-unit : is-prop unit
is-prop-unit = is-prop-is-contr is-contr-unit

is-prop' : {i : Level} (A : UU i) → UU i
is-prop' A = (x y : A) → Id x y

is-prop-is-prop' : {i : Level} {A : UU i} → is-prop' A → is-prop A
is-prop-is-prop' {i} {A} H x y =
  dpair
    (concat _ (inv (H x x)) (H x y))
    (ind-Id
      (λ z p → Id (concat _ (inv (H x x)) (H x z)) p)
      (left-inv (H x x)) y)

is-prop'-is-prop : {i : Level} {A : UU i} → is-prop A → is-prop' A
is-prop'-is-prop H x y = pr1 (H x y)

is-contr-is-prop-inh : {i : Level} {A : UU i} → is-prop A → A → is-contr A
is-contr-is-prop-inh H a = dpair a (is-prop'-is-prop H a)

is-subtype : {i j : Level} {A : UU i} (B : A → UU j) → UU (i ⊔ j)
is-subtype B = (x : _) → is-prop (B x)

-- Section 8.2 Sets

\end{code}
