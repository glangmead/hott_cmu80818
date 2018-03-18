\begin{code}

{-# OPTIONS --without-K #-}

module Lecture7 where

import Lecture6
open Lecture6 public

-- Section 7.1 Fiberwise equivalences
tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ({x : A} → B x → C x) → ( Σ A B → Σ A C)
tot f (dpair x y) = dpair x (f y)

fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : {x : A} → B x → C x) → (t : Σ A C) → fib (tot f) t → fib (f {pr1 t}) (pr2 t)
fib-ftr-fib-tot f .(dpair x (f y)) (dpair (dpair x y) refl) = dpair y refl

fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : {x : A} → B x → C x) → (t : Σ A C) → fib (f {pr1 t}) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (dpair a .(F y)) (dpair y refl) = dpair (dpair a y) refl

issec-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : {x : A} → B x → C x) → (t : Σ A C) → ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (dpair x .(f y)) (dpair y refl) = refl

isretr-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : {x : A} → B x → C x) → (t : Σ A C) → ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(dpair x (f y)) (dpair (dpair x y) refl) = refl

is-equiv-fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : {x : A} → B x → C x) → (t : Σ A C) → is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  pair
    (dpair (fib-tot-fib-ftr f t) (issec-fib-tot-fib-ftr f t))
    (dpair (fib-tot-fib-ftr f t) (isretr-fib-tot-fib-ftr f t))

\end{code}
