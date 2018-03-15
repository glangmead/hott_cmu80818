\begin{code}

{-# OPTIONS --without-K #-}

module Lecture3 where

import Lecture2
open Lecture2

data unit : U where
  star : unit
𝟙 = unit
ind-unit : {i : Level} {P : unit → UU i} → P star → ((x : unit) → P x)
ind-unit p star = p

data empty : U where
𝟘 = empty
ind-empty : {i : Level} {P : empty → UU i} → ((x : empty) → P x)
ind-empty ()

¬ : {i : Level} → UU i → UU i
¬ A = A → empty

data bool : U where
  true false : bool

data coprod {i j : Level} (A : UU i) (B : UU j) : UU (i ⊔ j)  where
  inl : A → coprod A B
  inr : B → coprod A B

data Sigma {i j : Level} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  dpair : (x : A) → (B x → Sigma A B)

Σ = Sigma

pr1 : {i j : Level} {A : UU i} {B : A → UU j} → Sigma A B → A
pr1 (dpair a b) = a

pr2 : {i j : Level} {A : UU i} {B : A → UU j} → (t : Sigma A B) → B (pr1 t)
pr2 (dpair a b) = b

prod : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
prod A B = Sigma A (λ a → B)

_×_ :  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A × B = prod A B

pair : {i j : Level} {A : UU i} {B : UU j} → A → (B → prod A B)
pair a b = dpair a b

-- Pointed types
U-pt : Type
U-pt = Sigma U (λ X → X)

-- Graphs
Gph : Type
Gph = Sigma U (λ X → (X → X → U))

-- Reflexive graphs
rGph : Type
rGph = Sigma U (λ X → Sigma (X → X → U) (λ R → (x : X) → R x x))

-- Finite sets
Fin : ℕ → U
Fin Nzero = empty
Fin (Nsucc n) = coprod (Fin n) unit

-- Observational equality on the natural numbers
EqN : ℕ → (ℕ → U)
EqN Nzero Nzero = 𝟙
EqN Nzero (Nsucc n) = 𝟘
EqN (Nsucc m) Nzero = 𝟘
EqN (Nsucc m) (Nsucc n) = EqN m n

-- The integers
ℤ : U
ℤ = coprod ℕ (coprod unit ℕ)

in-neg : ℕ → ℤ
in-neg n = inl n

Zneg-one : ℤ
Zneg-one = in-neg Nzero

Zzero : ℤ
Zzero = inr (inl star)

Zone : ℤ
Zone = inr (inr Nzero)

in-pos : ℕ → ℤ
in-pos n = inr (inr n)

-- Since Agda is already strong with nested induction, I dont think we need this definition.
ind-ℤ : {i : Level} (P : ℤ → UU i) → P Zneg-one → ((n : ℕ) → P (inl n) → P (inl (Nsucc n))) → P Zzero → P Zone → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (Nsucc n)))) → (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl Nzero) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (Nsucc x)) = p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr Nzero)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (Nsucc x))) = pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))

Zsucc : ℤ → ℤ
Zsucc (inl Nzero) = Zzero
Zsucc (inl (Nsucc x)) = inl x
Zsucc (inr (inl x)) = Zone
Zsucc (inr (inr x)) = inr (inr (Nsucc x))

-- Exercise 3.1
dne-dec : {i : Level} (A : UU i) → (coprod A (¬ A)) → (¬ (¬ A) → A)
dne-dec A (inl x) = λ t → x
dne-dec A (inr x) = λ f → ind-empty (f x)

-- Exercise 3.3
reflexive-EqN : (n : ℕ) → EqN n n
reflexive-EqN Nzero = star
reflexive-EqN (Nsucc n) = reflexive-EqN n

symmetric-EqN : (m n : ℕ) → EqN m n → EqN n m
symmetric-EqN Nzero Nzero t = t
symmetric-EqN Nzero (Nsucc n) t = t
symmetric-EqN (Nsucc n) Nzero t = t
symmetric-EqN (Nsucc m) (Nsucc n) t = symmetric-EqN m n t

transitive-EqN : (l m n : ℕ) → EqN l m → EqN m n → EqN l n
transitive-EqN Nzero Nzero Nzero s t = star
transitive-EqN (Nsucc n) Nzero Nzero s t = ind-empty s
transitive-EqN Nzero (Nsucc n) Nzero s t = ind-empty s
transitive-EqN Nzero Nzero (Nsucc n) s t = ind-empty t
transitive-EqN (Nsucc l) (Nsucc m) Nzero s t = ind-empty t
transitive-EqN (Nsucc l) Nzero (Nsucc n) s t = ind-empty s
transitive-EqN Nzero (Nsucc m) (Nsucc n) s t = ind-empty s
transitive-EqN (Nsucc l) (Nsucc m) (Nsucc n) s t = transitive-EqN l m n s t

-- Exercise 3.4
least-reflexive-EqN' : {i : Level} (n m : ℕ) (R : ℕ → ℕ → UU i) (ρ : (n : ℕ) → R n n) → EqN n m → R n m
least-reflexive-EqN' Nzero Nzero R ρ p = ρ Nzero
least-reflexive-EqN' Nzero (Nsucc m) R ρ = ind-empty
least-reflexive-EqN' (Nsucc n) Nzero R ρ = ind-empty
least-reflexive-EqN' (Nsucc n) (Nsucc m) R ρ = least-reflexive-EqN' n m (λ x y → R (Nsucc x) (Nsucc y)) (λ x → ρ (Nsucc x))

least-reflexive-EqN : {i : Level} {R : ℕ → ℕ → UU i} (ρ : (n : ℕ) → R n n) → (n m : ℕ) → EqN n m → R n m
least-reflexive-EqN ρ n m p = least-reflexive-EqN' n m _ ρ p

-- Exercise 3.5
preserve_EqN : (f : ℕ → ℕ) (n m : ℕ) → (EqN n m) → (EqN (f n) (f m))
preserve_EqN f = least-reflexive-EqN {_} {λ x y → EqN (f x) (f y)} (λ x → reflexive-EqN (f x))

-- Exercise 3.6

-- Definition of ≤ 
leqN : ℕ → ℕ → U
leqN Nzero Nzero = unit
leqN Nzero (Nsucc m) = unit
leqN (Nsucc n) Nzero = empty
leqN (Nsucc n) (Nsucc m) = leqN n m

-- Definition of <
leN : ℕ → ℕ → U
leN Nzero Nzero = empty
leN Nzero (Nsucc m) = unit
leN (Nsucc n) Nzero = empty
leN (Nsucc n) (Nsucc m) = leN n m

reflexive-leqN : (n : ℕ) → leqN n n
reflexive-leqN Nzero = star
reflexive-leqN (Nsucc n) = reflexive-leqN n

anti-reflexive-leN : (n : ℕ) → ¬ (leN n n)
anti-reflexive-leN Nzero = ind-empty
anti-reflexive-leN (Nsucc n) = anti-reflexive-leN n

transitive-leqN : (n m l : ℕ) → (leqN n m) → (leqN m l) → (leqN n l)
transitive-leqN Nzero Nzero Nzero p q = reflexive-leqN Nzero
transitive-leqN Nzero Nzero (Nsucc l) p q = q
transitive-leqN Nzero (Nsucc m) Nzero p q = star
transitive-leqN Nzero (Nsucc m) (Nsucc l) p q = star
transitive-leqN (Nsucc n) Nzero l p q = ind-empty p
transitive-leqN (Nsucc n) (Nsucc m) Nzero p q = ind-empty q
transitive-leqN (Nsucc n) (Nsucc m) (Nsucc l) p q = transitive-leqN n m l p q

transitive-leN : (n m l : ℕ) → (leN n m) → (leN m l) → (leN n l)
transitive-leN Nzero Nzero Nzero p q = p
transitive-leN Nzero Nzero (Nsucc l) p q = q
transitive-leN Nzero (Nsucc m) Nzero p q = ind-empty q
transitive-leN Nzero (Nsucc m) (Nsucc l) p q = star
transitive-leN (Nsucc n) Nzero l p q = ind-empty p
transitive-leN (Nsucc n) (Nsucc m) Nzero p q = ind-empty q
transitive-leN (Nsucc n) (Nsucc m) (Nsucc l) p q = transitive-leN n m l p q

succ-leN : (n : ℕ) → leN n (Nsucc n)
succ-leN Nzero = star
succ-leN (Nsucc n) = succ-leN n

-- Exercise 3.7
divides : (d n : ℕ) → U
divides d n = Sigma ℕ (λ m → EqN (d ** m) n)

-- Exercise 3.8
Eq2 : bool → bool → U
Eq2 true true = unit
Eq2 true false = empty
Eq2 false true = empty
Eq2 false false = unit

reflexive-Eq2 : (x : bool) → Eq2 x x
reflexive-Eq2 true = star
reflexive-Eq2 false = star

least-reflexive-Eq2 : {i : Level} (R : bool → bool → UU i) (ρ : (x : bool) → R x x) (x y : bool) → Eq2 x y → R x y
least-reflexive-Eq2 R ρ true true p = ρ true
least-reflexive-Eq2 R ρ true false p = ind-empty p
least-reflexive-Eq2 R ρ false true p = ind-empty p
least-reflexive-Eq2 R ρ false false p = ρ false

-- Exercise 3.9
t0 : coprod unit unit
t0 = inl star

t1 : coprod unit unit
t1 = inr star

ind-coprod-unit-unit : {i : Level} {P : coprod unit unit → UU i} → P t0 → P t1 → (x : coprod unit unit) → P x
ind-coprod-unit-unit p0 p1 (inl star) = p0
ind-coprod-unit-unit p0 p1 (inr star) = p1

-- Exercise 3.10
leqZ : ℤ → ℤ → U
leqZ (inl Nzero) (inl Nzero) = unit
leqZ (inl Nzero) (inl (Nsucc x)) = empty
leqZ (inl Nzero) (inr l) = unit
leqZ (inl (Nsucc x)) (inl Nzero) = unit
leqZ (inl (Nsucc x)) (inl (Nsucc y)) = leqZ (inl x) (inl y)
leqZ (inl (Nsucc x)) (inr l) = unit
leqZ (inr k) (inl x) = empty
leqZ (inr (inl star)) (inr l) = unit
leqZ (inr (inr x)) (inr (inl star)) = empty
leqZ (inr (inr Nzero)) (inr (inr y)) = unit
leqZ (inr (inr (Nsucc x))) (inr (inr Nzero)) = empty
leqZ (inr (inr (Nsucc x))) (inr (inr (Nsucc y))) = leqZ (inr (inr (x))) (inr (inr (y)))

reflexive-leqZ : (k : ℤ) → leqZ k k
reflexive-leqZ (inl Nzero) = star
reflexive-leqZ (inl (Nsucc x)) = reflexive-leqZ (inl x)
reflexive-leqZ (inr (inl star)) = star
reflexive-leqZ (inr (inr Nzero)) = star
reflexive-leqZ (inr (inr (Nsucc x))) = reflexive-leqZ (inr (inr x))

transitive-leqZ : (k l m : ℤ) → leqZ k l → leqZ l m → leqZ k m
transitive-leqZ (inl Nzero) (inl Nzero) m p q = q
transitive-leqZ (inl Nzero) (inl (Nsucc x)) m p q = ind-empty p
transitive-leqZ (inl Nzero) (inr (inl star)) (inl Nzero) star q = reflexive-leqZ (inl Nzero)
transitive-leqZ (inl Nzero) (inr (inl star)) (inl (Nsucc x)) star q = ind-empty q
transitive-leqZ (inl Nzero) (inr (inl star)) (inr (inl star)) star q = star
transitive-leqZ (inl Nzero) (inr (inl star)) (inr (inr x)) star q = star
transitive-leqZ (inl Nzero) (inr (inr x)) (inl y) star q = ind-empty q
transitive-leqZ (inl Nzero) (inr (inr x)) (inr (inl star)) star q = ind-empty q
transitive-leqZ (inl Nzero) (inr (inr x)) (inr (inr y)) star q = star
transitive-leqZ (inl (Nsucc x)) (inl Nzero) (inl Nzero) star q = star
transitive-leqZ (inl (Nsucc x)) (inl Nzero) (inl (Nsucc y)) star q = ind-empty q
transitive-leqZ (inl (Nsucc x)) (inl Nzero) (inr m) star q = star
transitive-leqZ (inl (Nsucc x)) (inl (Nsucc y)) (inl Nzero) p q = star
transitive-leqZ (inl (Nsucc x)) (inl (Nsucc y)) (inl (Nsucc z)) p q = transitive-leqZ (inl x) (inl y) (inl z) p q
transitive-leqZ (inl (Nsucc x)) (inl (Nsucc y)) (inr m) p q = star
transitive-leqZ (inl (Nsucc x)) (inr y) (inl z) star q = ind-empty q
transitive-leqZ (inl (Nsucc x)) (inr y) (inr z) star q = star
transitive-leqZ (inr k) (inl x) m p q = ind-empty p
transitive-leqZ (inr (inl star)) (inr l) (inl x) star q = ind-empty q
transitive-leqZ (inr (inl star)) (inr l) (inr m) star q = star
transitive-leqZ (inr (inr x)) (inr (inl star)) m p q = ind-empty p
transitive-leqZ (inr (inr Nzero)) (inr (inr Nzero)) m p q = q
transitive-leqZ (inr (inr Nzero)) (inr (inr (Nsucc y))) (inl x) star q = ind-empty q
transitive-leqZ (inr (inr Nzero)) (inr (inr (Nsucc y))) (inr (inl star)) star q = ind-empty q
transitive-leqZ (inr (inr Nzero)) (inr (inr (Nsucc y))) (inr (inr z)) star q = star
transitive-leqZ (inr (inr (Nsucc x))) (inr (inr Nzero)) m p q = ind-empty p
transitive-leqZ (inr (inr (Nsucc x))) (inr (inr (Nsucc y))) (inl z) p q = ind-empty q
transitive-leqZ (inr (inr (Nsucc x))) (inr (inr (Nsucc y))) (inr (inl star)) p q = ind-empty q
transitive-leqZ (inr (inr (Nsucc x))) (inr (inr (Nsucc y))) (inr (inr z)) p q = {!!}

succ-leqZ : (k l : ℤ) → leqZ k l → leqZ k (Zsucc l)
succ-leqZ (inl Nzero) (inl Nzero) p = star
succ-leqZ (inl Nzero) (inl (Nsucc y)) p = ind-empty p
succ-leqZ (inl (Nsucc x)) (inl Nzero) p = star
succ-leqZ (inl (Nsucc x)) (inl (Nsucc y)) p = succ-leqZ (inl (Nsucc x)) {!!} {!!}
succ-leqZ (inl x) (inr y) p = {!!}
succ-leqZ (inr k) l p = {!!}

leZ : ℤ → ℤ → U
leZ (inl Nzero) (inl x) = empty
leZ (inl Nzero) (inr y) = unit
leZ (inl (Nsucc x)) (inl Nzero) = unit
leZ (inl (Nsucc x)) (inl (Nsucc y)) = leZ (inl x) (inl y)
leZ (inl (Nsucc x)) (inr y) = unit
leZ (inr x) (inl y) = empty
leZ (inr (inl star)) (inr (inl star)) = empty
leZ (inr (inl star)) (inr (inr x)) = unit
leZ (inr (inr x)) (inr (inl star)) = empty
leZ (inr (inr Nzero)) (inr (inr Nzero)) = empty
leZ (inr (inr Nzero)) (inr (inr (Nsucc y))) = unit
leZ (inr (inr (Nsucc x))) (inr (inr Nzero)) = empty
leZ (inr (inr (Nsucc x))) (inr (inr (Nsucc y))) = leZ (inr (inr x)) (inr (inr y))

-- ind-leqZ : (k : ℤ) {i : Level} (P : (l : ℤ) (leqZ k l) → UU i) → P k (reflexive-leqZ k) → ((l : ℤ) (p : leqZ k l) → P l p → P (Zsucc l) (succ-leqZ l p)) → (l : ℤ) (p : leqZ k l) → P l p

\end{code}
