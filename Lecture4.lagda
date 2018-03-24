\begin{code}

{-# OPTIONS --without-K #-}

module Lecture4 where

import Lecture3
open Lecture3 public

-- the identity type on a type A, given a fixed basepoint x
data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

ind-Id : {i j : Level} {A : UU i} {x : A} (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x b y refl = b

-- groupoid structure on identity types (a.k.a. paths)

inv : {i : Level} {A : UU i} {x y : A} → Id x y → Id y x
inv (refl) = refl

concat : {i : Level} {A : UU i} {x z : A} (y : A) → Id x y → Id y z → Id x z
concat x refl q = q

_·_ : {i : Level} {A : UU i} {x z : A} {y : A} → Id x y → Id y z → Id x z
p · q = concat _ p q

assoc : {i : Level} {A : UU i} {x y z w : A} (p : Id x y) (q : Id y z) (r : Id z w) → Id (concat _ p (concat _ q r)) (concat _ (concat _ p q) r)
assoc refl q r = refl

left-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ refl p) p
left-unit refl = refl

right-unit : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (concat _ p refl) p
right-unit refl = refl

left-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ (inv p) p) refl
left-inv refl = refl

right-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) →
  Id (concat _ p (inv p)) refl
right-inv refl = refl

-- action on paths of a function

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

-- Exercise 4.1 The composition of transports is the transport of the concatenation
tr-concat : {i j : Level} {A : UU i} (B : A → UU j) {x y z : A} (p : Id x y) (q : Id y z) (b : B x) → Id (tr B q (tr B p b)) (tr B (concat _ p q) b)
tr-concat B refl refl b = refl

-- Exercise 4.2 Taking the inverse distributes contravariantly over concatenation
inv-assoc : {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) → Id (inv (concat _ p q)) (concat _ (inv q) (inv p))
inv-assoc refl refl = refl

-- Exercise 4.3 If B is a weakened family over A (trivial bundle, not dependent), then tr is refl
tr-triv : {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) → Id (tr (weaken A B) p b) b
tr-triv refl b = refl

-- Exercise 4.4 Transporting, using x=y and f:A → B, an identity between identities
tr-fib : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) →
  (q : Id (f x) b) → Id (tr (λ (a : A) → Id (f a) b) p q) (concat _ (inv (ap f p)) q)
tr-fib refl b q = refl

tr-fib' : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) →
  (q : Id b (f x)) → Id (tr (λ (a : A) → Id b (f a)) p q) (concat _ q (ap f p))
tr-fib' refl b refl = refl

-- Exercise 4.5
inv-con : {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) → (Id (p · q) r) → (Id q ((inv p) · r))
inv-con refl refl r refl = refl

con-inv : {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) → (Id (p · q) r) → (Id p (r · (inv q)))
con-inv refl refl r refl = refl

-- Exercise 4.6 Path lifting, from a path in the base A to a path in the total space Σ A B
lift : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B x) → Id (dpair x b) (dpair y (tr B p b))
lift refl b = refl

-- Exercise 4.7 Some laws of arithmetic (follow-up from Remark 2.3.1)
right-unit-addN : (m : ℕ) → Id (m + Nzero) m
right-unit-addN Nzero = refl
right-unit-addN (Nsucc m) = ap Nsucc (right-unit-addN m)

left-unit-addN : (m : ℕ) → Id (Nzero + m) m
left-unit-addN m = refl

assoc-addN : (m n k : ℕ) → Id (m + (n + k)) ((m + n) + k)
assoc-addN Nzero n k = refl
assoc-addN (Nsucc m) n k = ap Nsucc (assoc-addN m n k) 

right-succ-addN : (m n : ℕ) → Id (m + (Nsucc n)) (Nsucc (m + n))
right-succ-addN Nzero n = refl
right-succ-addN (Nsucc m) n = ap Nsucc (right-succ-addN m n)

comm-addN : (m n : ℕ) → Id (m + n) (n + m)
comm-addN Nzero Nzero = refl
comm-addN Nzero (Nsucc n) = ap Nsucc (comm-addN Nzero n)
comm-addN (Nsucc m) Nzero = ap Nsucc (comm-addN m Nzero)
comm-addN (Nsucc m) (Nsucc n) =
  (ap Nsucc (comm-addN m (Nsucc n))) · (inv (right-succ-addN (Nsucc n) m))

right-zero-mulN : (m : ℕ) → Id (m ** Nzero) Nzero
right-zero-mulN Nzero = refl
right-zero-mulN (Nsucc m) = concat (m ** Nzero) (right-unit-addN _) (right-zero-mulN m)

-- nat-mult-is-assoc : (m n k : ℕ) → Id (m ** (n ** k)) ((m ** n) ** k)
-- nat-mult-is-assoc Nzero Nzero Nzero = refl
-- nat-mult-is-assoc Nzero Nzero (Nsucc k) = refl
-- nat-mult-is-assoc Nzero (Nsucc n) Nzero = refl
-- nat-mult-is-assoc Nzero (Nsucc n) (Nsucc k) = refl
-- nat-mult-is-assoc (Nsucc m) Nzero Nzero = refl
-- nat-mult-is-assoc (Nsucc m) Nzero (Nsucc k) = refl
-- nat-mult-is-assoc (Nsucc m) (Nsucc n) Nzero = refl
-- nat-mult-is-assoc (Nsucc m) Nzero Nzero = refl

N1 = Nsucc Nzero

-- nat-left-mult-identity : (m : ℕ) → Id (m ** N1) m
-- nat-left-mult-identity Nzero = {!   !}
-- nat-left-mult-identity (Nsucc m) = {!   !}
--
-- nat-right-mult-identity : (m : ℕ) → Id (N1 ** m) m
-- nat-right-mult-identity Nzero = {!   !}
-- nat-right-mult-identity (Nsucc m) = {!   !}
--
-- nat-mult-com : (m n : ℕ) → Id (m ** n) (n ** m)
-- nat-mult-com Nzero Nzero = {!   !}
-- nat-mult-com Nzero (Nsucc n) = {!   !}
-- nat-mult-com (Nsucc m) Nzero = {!   !}
-- nat-mult-com (Nsucc m) (Nsucc n) = {!   !}
--
-- nat-mult-distr : (m n k : ℕ) → Id (m ** (n + k)) ((m ** n) + (m ** k))
-- nat-mult-distr Nzero Nzero Nzero = {!   !}
-- nat-mult-distr Nzero Nzero (Nsucc k) = {!   !}
-- nat-mult-distr Nzero (Nsucc n) Nzero = {!   !}
-- nat-mult-distr Nzero (Nsucc n) (Nsucc k) = {!   !}
-- nat-mult-distr (Nsucc m) Nzero Nzero = {!   !}
-- nat-mult-distr (Nsucc m) Nzero (Nsucc k) = {!   !}
-- nat-mult-distr (Nsucc m) (Nsucc n) Nzero = {!   !}
-- nat-mult-distr (Nsucc m) (Nsucc n) (Nsucc k) = {!   !}

\end{code}
