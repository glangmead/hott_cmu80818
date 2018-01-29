module Playground where

-- Equality type, and its only constructor refl
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

-- identity map of a type
id : {A : Set} → A → A
id x = x

-- action on paths
ap : {A B : Set} (f : A → B) {x y : A} → (x == y -> f x == f y)
ap f refl = refl

-- transport
transport : {A : Set} (B : A → Set) {x y : A} (p : x == y) → (B x → B y)
transport _ refl = id

-- Pi types
Π : (A : Set) (P : A → Set) → Set
Π A P = (x : A) → P x

-- Sigma types
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

-- empty type
data ⊥ : Set where

-- not operator
¬ : (A : Set) → Set
¬ A = A → ⊥
