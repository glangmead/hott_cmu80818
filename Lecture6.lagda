\begin{code}

{-# OPTIONS --without-K #-}

module Lecture6 where

import Lecture5
open Lecture5 public

-- Section 6.1 Contractible types

is-contr : {i : Level} → UU i → UU i
is-contr A = Sigma A (λ a → (x : A) → Id a x)

center : {i : Level} {A : UU i} → is-contr A → A
center (dpair c C) = c

-- We make sure that the contraction is coherent in a straightforward way
contraction : {i : Level} {A : UU i} (H : is-contr A) →
  (const A A (center H) ~ id)
contraction (dpair c C) x = concat _ (inv (C c)) (C x)

coh-contraction : {i : Level} {A : UU i} (H : is-contr A) →
  Id (contraction H (center H)) refl
coh-contraction (dpair c C) = left-inv (C c)

ev-pt : {i j : Level} (A : UU i) (a : A) (B : A → UU j) → ((x : A) → B x) → B a
ev-pt A a B f = f a

sing-ind-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) →
  B (center H) → (x : A) → B x
sing-ind-is-contr A H B b x = tr B (contraction H x) b

sing-comp-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) →
  (((ev-pt A (center H) B) ∘ (sing-ind-is-contr A H B)) ~ id)
sing-comp-is-contr A H B b =
  ap (λ (ω : Id (center H) (center H)) → tr B ω b) (coh-contraction H)

is-sing-is-contr : {i j : Level} (A : UU i) (H : is-contr A) (B : A → UU j) → sec (ev-pt A (center H) B)
is-sing-is-contr A H B = dpair (sing-ind-is-contr A H B) (sing-comp-is-contr A H B)

is-sing : {i : Level} (A : UU i) → A → UU (lsuc i)
is-sing {i} A a = (B : A → UU i) → sec (ev-pt A a B)

is-contr-is-sing : {i : Level} (A : UU i) (a : A) →
  is-sing A a → is-contr A
is-contr-is-sing A a S = dpair a (pr1 (S (λ y → Id a y)) refl)

is-sing-unit : is-sing unit star
is-sing-unit B = dpair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-sing unit star (is-sing-unit)

is-sing-total-path : {i : Level} (A : UU i) (a : A) →
  is-sing (Σ A (λ x → Id a x)) (dpair a refl)
is-sing-total-path A a B = dpair (ind-Σ ∘ ind-Id) (λ b → refl)

is-contr-total-path : {i : Level} (A : UU i) (a : A) →
  is-contr (Σ A (λ x → Id a x))
is-contr-total-path A a = is-contr-is-sing _ _ (is-sing-total-path A a)

-- Section 6.2 Contractible maps

fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

is-contr-map : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

-- Our goal is to show that contractible maps are equivalences. First we construct the inverse of a contractible map.
inv-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
inv-is-contr-map H y = pr1 (center (H y))

-- Then we show that the inverse is a section.
issec-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (H : is-contr-map f) → (f ∘ (inv-is-contr-map H)) ~ id
issec-is-contr-map H y = pr2 (center (H y))

-- Then we show that the inverse is also a retraction.
isretr-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (H : is-contr-map f) → ((inv-is-contr-map H) ∘ f) ~ id
isretr-is-contr-map {_} {_} {A} {B} {f} H x =
  ap {_} {_} {fib f (f x)} {A} pr1
    {dpair (inv-is-contr-map H (f x)) (issec-is-contr-map H (f x))}
    {dpair x refl}
    ( concat (center (H (f x)))
             (inv (contraction (H (f x))
               (dpair (inv-is-contr-map H (f x)) (issec-is-contr-map H (f x)))))
             (contraction (H (f x)) (dpair x refl)))

-- Finally we put it all together to show that contractible maps are equivalences.
is-equiv-is-contr-map : {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → is-equiv f
is-equiv-is-contr-map H =
  pair
    (dpair (inv-is-contr-map H) (issec-is-contr-map H))
    (dpair (inv-is-contr-map H) (isretr-is-contr-map H))

\end{code}
