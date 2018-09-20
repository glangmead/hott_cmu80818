\begin{code}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Lecture7 where

import Lecture6
open Lecture6 public

-- Section 7.1 Fiberwise equivalences
tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f (dpair x y) = dpair x (f x y)

-- There is a function from the fibers of the induced map on total spaces, to the fibers of the fiberwise transformation
fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(dpair x (f x y)) (dpair (dpair x y) refl) = dpair y refl

-- This function has a converse
fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (dpair a .(F a y)) (dpair y refl) = dpair (dpair a y) refl

issec-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (dpair x .(f x y)) (dpair y refl) = refl

isretr-fib-tot-fib-ftr : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(dpair x (f x y)) (dpair (dpair x y) refl) = refl

-- We establish that the fibers of the induced map on total spaces are equivalent to the fibers of the fiberwise transformation.
is-equiv-fib-ftr-fib-tot : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → (f : (x : A) → B x → C x) → (t : Σ A C) → is-equiv (fib-ftr-fib-tot f t)
is-equiv-fib-ftr-fib-tot f t =
  pair
    (dpair (fib-tot-fib-ftr f t) (issec-fib-tot-fib-ftr f t))
    (dpair (fib-tot-fib-ftr f t) (isretr-fib-tot-fib-ftr f t))

-- Any fiberwise equivalence induces an equivalence on total spaces
is-fiberwise-equiv : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

is-equiv-tot-is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-fiberwise-equiv f →
  is-equiv (tot f )
is-equiv-tot-is-fiberwise-equiv f H =
  is-equiv-is-contr-map
    (λ t → is-contr-is-equiv
      (fib-ftr-fib-tot f t)
      (is-equiv-fib-ftr-fib-tot f t)
      (is-contr-map-is-equiv (H _) (pr2 t)))

-- Convesely, any fiberwise transformation that induces an equivalence on total spaces is a fiberwise equivalence.
is-fiberwise-equiv-is-equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → is-equiv (tot f) →
  is-fiberwise-equiv f
is-fiberwise-equiv-is-equiv-tot f H x =
  is-equiv-is-contr-map
    (λ z → is-contr-is-equiv'
      (fib-ftr-fib-tot f (dpair x z))
      (is-equiv-fib-ftr-fib-tot f (dpair x z))
      (is-contr-map-is-equiv H (dpair x z)))

-- Section 7.2 The fundamental theorem

-- The general form of the fundamental theorem of identity types
id-fundamental-gen : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) → is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
id-fundamental-gen {_} {_} {A} {B} a b C f x =
  is-fiberwise-equiv-is-equiv-tot f
    (is-equiv-is-contr _ (is-contr-total-path A a) C) x

-- The canonical form of the fundamental theorem of identity types
id-fundamental : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
id-fundamental {i} {j} {A} {B} a b H =
  id-fundamental-gen a b H (ind-Id a (λ x p → B x) b)

-- The converse of the fundamental theorem of identity types
id-fundamental' : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
id-fundamental' {i} {j} {A} {B} a b H =
  is-contr-is-equiv'
    (tot (ind-Id a (λ x p → B x) b))
    (is-equiv-tot-is-fiberwise-equiv _ H)
    (is-contr-total-path A a)

-- As an application we show that equivalences are embeddings.
is-emb : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

is-emb-is-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} f E x =
  id-fundamental-gen x refl
    (is-contr-is-equiv' (tot (λ y (p : Id (f y) (f x)) → inv p))
        (is-equiv-tot-is-fiberwise-equiv _ (λ y → is-equiv-inv (f y) (f x)))
      (is-contr-map-is-equiv E (f x)))
    (λ y p → ap f p)

-- Exercises

-- Exercise 7.1

tot-htpy : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (dpair x y) = eq-pair (dpair refl (H x y))

tot-id : {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (dpair x y) = refl

tot-comp : {i j j' j'' : Level} {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''} (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (dpair x y) = refl

-- Exercise 7.2
fib' : {i j : Level} {A : UU i} {B : UU j} → (A → B) → B → UU (i ⊔ j)
fib' f y = Σ _ (λ x → Id y (f x))

fib'-fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) → fib f y → fib' f y
fib'-fib f y t = tot (λ x → inv) t

is-equiv-fib'-fib : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) → is-equiv (fib'-fib f y)
is-equiv-fib'-fib f y = is-equiv-tot-is-fiberwise-equiv (λ x → inv) (λ x → is-equiv-inv (f x) y)

-- Exercise 7.7
id-fundamental-retr : {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
  (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
  (x : A) → is-equiv (i x)
id-fundamental-retr {_} {_} {A} {B} a i R =
  is-fiberwise-equiv-is-equiv-tot i
    (is-equiv-is-contr (tot i)
      (is-contr-retract-of (Σ _ (λ y → Id a y))
        (dpair (tot i)
          (dpair (tot λ x → pr1 (R x))
            (htpy-concat
              (tot (λ x → pr1 (R x) ∘ i x))
              (htpy-inv (tot-comp i (λ x → pr1 (R x))))
                (htpy-concat (tot (λ x → id))
                  (tot-htpy λ x → pr2 (R x))
                  (tot-id B)))))
        (is-contr-total-path _ a))
      (is-contr-total-path _ a))

-- Exercise 7.12

coherence-reduction-map : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (α : (x : A) → B x → Id a x) →
  (Σ (B a) (λ b → Id (α a b) refl)) → Σ A B
coherence-reduction-map a α (dpair b p) = dpair a b

is-contr-coherence-reduction-map : {i j : Level} {A : UU i} {B : A → UU j} (a : A) (α : (x : A) → B x → Id a x) → is-contr-map (coherence-reduction-map a α)
is-contr-coherence-reduction-map a α (dpair x y) = {!!}

\end{code}
