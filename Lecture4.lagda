\begin{code}

{-# OPTIONS --without-K #-}

module Lecture4 where

import Lecture3
open Lecture3 public

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

inv : {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv (refl) = refl

concat : {i : Level} {A : UU i} {x : A} (y : A) {z : A} → Id x y → Id y z → Id x z
concat x refl q = q

assoc : {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z) (r : Id z w) → Id (concat _ p (concat _ q r)) (concat _ (concat _ p q) r)
assoc refl q r = refl

left-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ refl p) p
left-unit p = refl

right-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ p refl) p
right-unit refl = refl

left-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ (inv p) p) refl
left-inv refl = refl

right-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ p (inv p)) refl
right-inv refl = refl

ap : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (f x) (f y)
ap f refl = refl

ap-id : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C) (f : A → B) {x y : A} (p : Id x y) → Id (ap (comp g f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-refl : {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x : A) →
  Id (ap f (refl {_} {_} {x})) refl
ap-refl f x = refl

ap-concat : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y z : A} (p : Id x y) (q : Id y z) → Id (ap f (concat _ p q)) (concat _ (ap f p) (ap f q))
ap-concat f refl q = refl

ap-inv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (ap f (inv p)) (inv (ap f p))
ap-inv f refl = refl

tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) (b : B x) → B y
tr B refl b = b

apd : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A} (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

\end{code}
