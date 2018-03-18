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

is-equiv-tot-is-equiv-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : {x : A} → B x → C x) → ((x : A) → is-equiv (f {x})) →
  is-equiv (tot {i} {j} {k} {A} {B} {C} f )
is-equiv-tot-is-equiv-ftr f H =
  is-equiv-is-contr-map
    (λ t → is-contr-is-equiv
      (fib-ftr-fib-tot f t)
      (is-equiv-fib-ftr-fib-tot f t)
      (is-contr-map-is-equiv (H _) (pr2 t)))

is-equiv-ftr-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : {x : A} → B x → C x) → is-equiv (tot {_} {_} {_} {A} {B} {C} f) →
  (x : A) → is-equiv (f {x})
is-equiv-ftr-is-equiv-tot f H x =
  is-equiv-is-contr-map
    (λ z → is-contr-is-equiv'
      (fib-ftr-fib-tot f (dpair x z))
      (is-equiv-fib-ftr-fib-tot f (dpair x z))
      (is-contr-map-is-equiv H (dpair x z)))

-- Section 7.2 The fundamental theorem
canonical : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  {x : A} → Id a x → B x
canonical a b refl = b

id-fundamental : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) →
  (x : A) → is-equiv (canonical {i} {j} {A} {B} a b {x})
id-fundamental {i} {j} {A} {B} a b H x =
  is-equiv-ftr-is-equiv-tot {i} {i} {j} {A} {λ x₁ → Id a x₁} {B}
    (canonical {i} {j} {A} {B} a b)
    (is-equiv-is-contr _ (is-contr-total-path A a) H)
    x

id-fundamental' : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  ((x : A) → is-equiv (canonical {i} {j} {A} {B} a b {x})) → is-contr (Σ A B)
id-fundamental' {i} {j} {A} {B} a b H =
  is-contr-is-equiv'
    (tot (canonical {i} {j} {A} {B} a b))
    (is-equiv-tot-is-equiv-ftr _ H)
    (is-contr-total-path A a)

\end{code}
