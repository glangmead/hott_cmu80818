\begin{code}

{-# OPTIONS --without-K #-}

module Lecture4 where

import Lecture3
open Lecture3 public

data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

ind-Id : {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b

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

-- Exercise 4.1
tr-concat : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) {z : A} (q : Id y z) (b : B x) → Id (tr B q (tr B p b)) (tr B (concat y p q) b)
tr-concat refl q b = refl

-- Exercise 4.2
inv-assoc : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) → Id (inv (concat _ p q)) (concat _ (inv q) (inv p))
inv-assoc refl refl = refl

-- Exercise 4.3
tr-triv : {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) → Id (tr (λ (a : A) → B) p b) b
tr-triv refl b = refl

apd-triv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) → Id (apd f p) (concat (f x) (tr-triv p (f x)) (ap f p))
apd-triv f refl = refl

-- Exercise 4.4
tr-fib : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) →
  (q : Id (f x) b) → Id (tr (λ (a : A) → Id (f a) b) p q) (concat _ (inv (ap f p)) q)
tr-fib refl b q = refl

tr-fib' : {i j : Level} {A : UU i} {B : UU j} {f : A → B} {x y : A} (p : Id x y) (b : B) → (q : Id b (f x)) → Id (tr (λ (a : A) → Id b (f a)) p q) (concat _ q (ap f p))
tr-fib' refl b q = inv (right-unit q)

-- Exercise 4.5
inv-con : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id q (concat _ (inv p) r)
inv-con refl q r s = s

con-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z) (r : Id x z) → (Id (concat _ p q) r) → Id p (concat _ r (inv q))
con-inv refl refl _ refl = refl

-- Exercise 4.6
lift : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B x) → Id (dpair x b) (dpair y (tr B p b))
lift refl b = refl

-- Exercise 4.7
add-assoc : (x y z : ℕ) → Id (add (add x y) z) (add x (add y z))
add-assoc Nzero y z = refl 
add-assoc (Nsucc x) y z = ap Nsucc (add-assoc x y z)

add-zero : (x : ℕ) → Id (add x Nzero) x
add-zero Nzero = refl
add-zero (Nsucc x) = ap Nsucc (add-zero x)

zero-add : (x : ℕ) → Id (add Nzero x) x
zero-add x = refl

Nsucc-add : (x y : ℕ) → Id (add (Nsucc x) y) (Nsucc (add x y))
Nsucc-add x y = refl

add-Nsucc : (x y : ℕ) → Id (add x (Nsucc y)) (Nsucc (add x y))
add-Nsucc Nzero y = refl
add-Nsucc (Nsucc x) y = ap Nsucc (add-Nsucc x y)

add-comm : (x y : ℕ) → Id (add x y) (add y x)
add-comm Nzero y = inv (add-zero y)
add-comm (Nsucc x) y = concat _ (ap Nsucc (add-comm x y)) (inv (add-Nsucc y x))

Nmul-one : (x : ℕ) → Id (x ** (Nsucc Nzero)) x
Nmul-one Nzero = refl
Nmul-one (Nsucc x) =
  concat _
    (add-Nsucc (x ** (Nsucc Nzero)) Nzero)
    (ap Nsucc (concat _ (add-zero _) (Nmul-one x)))

one-Nmul : (x : ℕ) → Id ((Nsucc Nzero) ** x) x
one-Nmul x = refl

Nsucc-Nmul : (x y : ℕ) → Id ((Nsucc x) ** y) (add (x ** y) y)
Nsucc-Nmul x y = refl

Nmul-Nsucc : (x y : ℕ) → Id (x ** (Nsucc y)) (add x (x ** y))
Nmul-Nsucc Nzero y = refl
Nmul-Nsucc (Nsucc x) y =
  concat (Nsucc (add (x ** (Nsucc y)) y))
    (add-Nsucc (x ** (Nsucc y)) y)
    (concat (Nsucc (add (add x (x ** y)) y))
      (ap (λ t → Nsucc (add t y)) (Nmul-Nsucc x y))
      (ap Nsucc (add-assoc x (x ** y) y)))

distr-add-mul : (x y z : ℕ) → Id (x ** (add y z)) (add (x ** y) (x ** z))
distr-add-mul Nzero y z = refl
distr-add-mul (Nsucc x) y z =
  concat _
    (Nsucc-Nmul x (add y z))
    (concat _
      (ap (λ t → add t (add y z)) (distr-add-mul x y z))
      (concat (add (x ** y) (add (x ** z) (add y z)))
        (add-assoc (x ** y) (x ** z) (add y z))
        (concat _
          (ap (add (x ** y)) (concat _
            (inv (add-assoc (x ** z) y z))
            (concat _
              (ap (λ t → add t z) (add-comm (x ** z) y))
              (add-assoc y (x ** z) z))))
          (inv (add-assoc (x ** y) y (add (x ** z) z))))))

Nzero-mul : (x : ℕ) → Id (Nzero ** x) Nzero
Nzero-mul x = refl

mul-Nzero : (x : ℕ) → Id (x ** Nzero) Nzero
mul-Nzero Nzero = refl
mul-Nzero (Nsucc x) = concat _ (add-zero (x ** Nzero)) (mul-Nzero x)

mul-comm : (x y : ℕ) → Id (x ** y) (y ** x)
mul-comm Nzero y = inv (mul-Nzero y)
mul-comm (Nsucc x) y = concat _ (add-comm (x ** y) y) (concat _ (ap (add y) (mul-comm x y)) (inv (Nmul-Nsucc y x)))

distr-add-mul' : (x y z : ℕ) → Id ((add x y) ** z) (add (x ** z) (y ** z))
distr-add-mul' x y z = concat _ (mul-comm (add x y) z) (concat _ (distr-add-mul z x y) (concat _ (ap (λ t → add t (z ** y)) (mul-comm z x)) (ap (λ t → add (x ** z) t) (mul-comm z y))))

mul-assoc : (x y z : ℕ) → Id ((x ** y) ** z) (x ** (y ** z))
mul-assoc Nzero y z = refl
mul-assoc (Nsucc x) y z =
  concat _
    (distr-add-mul' (x ** y) y z)
    (ap (λ t → add t (y ** z)) (mul-assoc x y z))

\end{code}
