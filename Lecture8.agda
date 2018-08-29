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

is-set : {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

axiom-K : {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : Id x x) → Id refl p

is-set-axiom-K : {i : Level} (A : UU i) → axiom-K A → is-set A
is-set-axiom-K A H x y =
  is-prop-is-prop' (ind-Id (λ z p → (q : Id x z) → Id p q) (H x) y)

axiom-K-is-set : {i : Level} (A : UU i) → is-set A → axiom-K A
axiom-K-is-set A H x p =
  concat
    (center (is-contr-is-prop-inh (H x x) refl))
      (inv (contraction (is-contr-is-prop-inh (H x x) refl) refl))
      (contraction (is-contr-is-prop-inh (H x x) refl) p)

is-equiv-prop-in-id : {i j : Level} {A : UU i}
  (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y)
  → (x y : A) → is-equiv (i x y)
is-equiv-prop-in-id R p ρ i x =
  id-fundamental-retr x (i x)
    (λ y → dpair
      (ind-Id (λ z p → R x z) (ρ x) y)
      ((λ r → is-prop'-is-prop (p x y) _ r)))

is-prop-is-equiv : {i j : Level} {A : UU i} (B : UU j)
  (f : A → B) (E : is-equiv f) → is-prop B → is-prop A
is-prop-is-equiv B f E H x y =
  is-contr-is-equiv (ap f {x} {y}) (is-emb-is-equiv f E x y) (H (f x) (f y))

is-prop-is-equiv' : {i j : Level} (A : UU i) {B : UU j}
  (f : A → B) (E : is-equiv f) → is-prop A → is-prop B
is-prop-is-equiv' A f E H =
  is-prop-is-equiv _ (inv-is-equiv E) (is-equiv-inv-is-equiv E) H

is-set-prop-in-id : {i j : Level} {A : UU i}
  (R : A → A → UU j)
  (p : (x y : A) → is-prop (R x y))
  (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → Id x y)
  → is-set A
is-set-prop-in-id R p ρ i x y = is-prop-is-equiv' (R x y) (i x y) (is-equiv-prop-in-id R p ρ i x y) (p x y)

is-prop-EqN : (n m : ℕ) → is-prop (EqN n m)
is-prop-EqN Nzero Nzero = is-prop-unit
is-prop-EqN Nzero (Nsucc m) = is-prop-empty
is-prop-EqN (Nsucc n) Nzero = is-prop-empty
is-prop-EqN (Nsucc n) (Nsucc m) = is-prop-EqN n m

is-set-nat : is-set ℕ
is-set-nat =
  is-set-prop-in-id
    EqN
    is-prop-EqN
    reflexive-EqN
    (least-reflexive-EqN (λ n → refl))
