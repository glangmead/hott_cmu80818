\begin{code}

{-# OPTIONS --without-K #-}

module Lecture5 where

import Lecture4
open Lecture4 public

_~_ : {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → Id (f x) (g x)

htpy-refl : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → f ~ f
htpy-refl f x = refl

htpy-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} → (f ~ g) → (g ~ f)
htpy-inv H x = inv (H x)

htpy-concat : {i j : Level} {A : UU i} {B : A → UU j} {f g h : (x : A) → B x} → (f ~ g) → (g ~ h) → (f ~ h)
htpy-concat H K x = concat (H x) (K x)

htpy-assoc : {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} → (H : f ~ g) → (K : g ~ h) → (L : h ~ k) → htpy-concat H (htpy-concat K L) ~ htpy-concat (htpy-concat H K) L
htpy-assoc H K L x = assoc (H x) (K x) (L x)

htpy-left-unit : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → (htpy-concat (htpy-refl f) H) ~ H
htpy-left-unit H x = left-unit (H x)

htpy-right-unit : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → (htpy-concat H (htpy-refl g)) ~ H
htpy-right-unit H x = right-unit (H x)

htpy-left-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → htpy-concat (htpy-inv H) H ~ htpy-refl g
htpy-left-inv H x = left-inv (H x)

htpy-right-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → htpy-concat H (htpy-inv H) ~ htpy-refl f
htpy-right-inv H x = right-inv (H x)

left-whisk : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
left-whisk h H x = ap h (H x)

right-whisk : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
right-whisk H f x = H (f x)

\end{code}
