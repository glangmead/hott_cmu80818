\begin{code}

{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Lecture5 where

import Lecture4
open Lecture4 public


-- Section 5.1 Homotopies
_~_ : {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → Id (f x) (g x)

htpy-refl : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → f ~ f
htpy-refl f x = refl

htpy-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} → (f ~ g) → (g ~ f)
htpy-inv H x = inv (H x)

htpy-concat : {i j : Level} {A : UU i} {B : A → UU j} {f : (x : A) → B x} (g : (x : A) → B x) {h : (x : A) → B x} → (f ~ g) → (g ~ h) → (f ~ h)
htpy-concat g H K x = concat _ (H x) (K x)

htpy-assoc : {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} → (H : f ~ g) → (K : g ~ h) → (L : h ~ k) → htpy-concat _ H (htpy-concat _ K L) ~ htpy-concat _ (htpy-concat _ H K) L
htpy-assoc H K L x = assoc (H x) (K x) (L x)

htpy-left-unit : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → (htpy-concat _ (htpy-refl f) H) ~ H
htpy-left-unit H x = left-unit (H x)

htpy-right-unit : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → (htpy-concat _ H (htpy-refl g)) ~ H
htpy-right-unit H x = right-unit (H x)

htpy-left-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → htpy-concat _ (htpy-inv H) H ~ htpy-refl g
htpy-left-inv H x = left-inv (H x)

htpy-right-inv : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} (H : f ~ g) → htpy-concat _ H (htpy-inv H) ~ htpy-refl f
htpy-right-inv H x = right-inv (H x)

htpy-left-whisk : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

htpy-right-whisk : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

-- Section 5.2 Bi-invertible maps
sec : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {_} {_} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

retr : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {_} {_} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ : {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

is-equiv : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ : {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

eqv-map : {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
eqv-map e = pr1 e

is-equiv-eqv-map : {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (eqv-map e)
is-equiv-eqv-map e = pr2 e

eqv-sec : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → sec f
eqv-sec e = pr1 e

eqv-secf : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
eqv-secf e = pr1 (eqv-sec e)

eqv-sech : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → (e : is-equiv f) → ((f ∘ eqv-secf e) ~ id)
eqv-sech e = pr2 (eqv-sec e)

eqv-retr : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → retr f
eqv-retr e = pr2 e

eqv-retrf : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
eqv-retrf e = pr1 (eqv-retr e)

eqv-retrh : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → (e : is-equiv f) → (((eqv-retrf e) ∘ f) ~ id)
eqv-retrh e = pr2 (eqv-retr e)

is-invertible : {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-invertible {_} {_} {A} {B} f = Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

is-equiv-is-invertible : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-invertible f → is-equiv f
is-equiv-is-invertible (dpair g (dpair H K)) = pair (dpair g H) (dpair g K)

htpy-secf-retrf : {i j : Level} {A : UU i} {B : UU j} {f : A → B} (e : is-equiv f) → (eqv-secf e ~ eqv-retrf e)
htpy-secf-retrf {_} {_} {_} {_} {f} (dpair (dpair g issec) (dpair h isretr)) =
  htpy-concat (h ∘ (f ∘ g)) (htpy-inv (htpy-right-whisk isretr g)) (htpy-left-whisk h issec)

is-invertible-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → is-invertible f
is-invertible-is-equiv {_} {_} {_} {_} {f} (dpair (dpair g issec) (dpair h isretr)) = dpair g (pair issec (htpy-concat (h ∘ f) (htpy-right-whisk (htpy-secf-retrf (dpair (dpair g issec) (dpair h isretr))) f) isretr))

inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
inv-is-equiv E = pr1 (is-invertible-is-equiv E)

issec-inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → (E : is-equiv f) → (f ∘ (inv-is-equiv E)) ~ id
issec-inv-is-equiv E = pr1 (pr2 (is-invertible-is-equiv E))

isretr-inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → (E : is-equiv f) → ((inv-is-equiv E) ∘ f) ~ id
isretr-inv-is-equiv E = pr2 (pr2 (is-invertible-is-equiv E))

is-equiv-inv-is-equiv : {i j : Level} {A : UU i} {B : UU j} {f : A → B} → (E : is-equiv f) → is-equiv (inv-is-equiv E)
is-equiv-inv-is-equiv {_} {_} {_} {_} {f} E =
  pair (dpair f (isretr-inv-is-equiv E)) (dpair f (issec-inv-is-equiv E))

is-equiv-id : {i : Level} (A : UU i) → is-equiv (id {_} {A})
is-equiv-id A = pair (dpair id (htpy-refl id)) (dpair id (htpy-refl id))


inv-Pi-swap : {i j k : Level} {A : UU i} {B : UU j} (C : A → B → UU k) →
  ((y : B) (x : A) → C x y) → ((x : A) (y : B) → C x y)
inv-Pi-swap C g x y = g y x

is-equiv-swap : {i j k : Level} {A : UU i} {B : UU j} (C : A → B → UU k) → is-equiv (Pi-swap {_} {_} {_} {A} {B} {C})
is-equiv-swap C = pair (dpair (inv-Pi-swap C) (htpy-refl id)) (dpair (inv-Pi-swap C) (htpy-refl id))

-- Section 5.3 The identity type of a Σ-type

eq-pair' : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → (Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))) → Id s t
eq-pair' (dpair x y) (dpair x' y') (dpair refl refl) = refl

eq-pair : {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} → (Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))) → Id s t
eq-pair {i} {j} {A} {B} {s} {t} = eq-pair' s t

pair-eq' : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → (Id s t) → Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))
pair-eq' s t refl = dpair refl refl

pair-eq  : {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} → (Id s t) → Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))
pair-eq {i} {j} {A} {B} {s} {t} = pair-eq' s t

isretr-pair-eq : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → (((pair-eq' s t) ∘ (eq-pair' s t)) ~ id)
isretr-pair-eq (dpair x y) (dpair x' y') (dpair refl refl) = refl

issec-pair-eq : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → (((eq-pair' s t) ∘ (pair-eq' s t)) ~ id)
issec-pair-eq (dpair x y) .(dpair x y) refl = refl

is-equiv-eq-pair' : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → is-equiv (eq-pair' s t)
is-equiv-eq-pair' s t = pair (dpair (pair-eq' s t) (issec-pair-eq s t)) (dpair (pair-eq' s t) (isretr-pair-eq s t))

is-equiv-eq-pair : {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → is-equiv (eq-pair {i} {j} {A} {B} {s} {t})
is-equiv-eq-pair = is-equiv-eq-pair'

-- We also define a function eq-pair-triv, which is like eq-pair but simplified for the case where B is just a type.

eq-pair-triv : {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) → prod (Id (pr1 s) (pr1 t)) (Id (pr2 s) (pr2 t)) → Id s t
eq-pair-triv (dpair x y) (dpair .x .y) (dpair refl refl) = refl

-- Ideally, we would use the 3-for-2 property of equivalences to show that eq-pair-triv is an equivalence, using that eq-pair is an equivalence. Indeed, there is an equivalence (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). However, to show that this map is an equivalence we either give a direct proof (in which case we might as well have given a direct proof that eq-pair-triv is an equivalence), or we use the fact that it is the induced map on total spaces of a fiberwise equivalence (the topic of Lecture 7). Thus it seems that a direct proof showing that eq-pair-triv is an equivalence is quickest for now. 

pair-eq-triv : {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) → Id s t → prod (Id (pr1 s) (pr1 t)) (Id (pr2 s) (pr2 t))
pair-eq-triv s .s refl = pair refl refl

isretr-pair-eq-triv : {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) → ((pair-eq-triv s t) ∘ (eq-pair-triv s t)) ~ id
isretr-pair-eq-triv (dpair x y) (dpair .x .y) (dpair refl refl) = refl

issec-pair-eq-triv : {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) → ((eq-pair-triv s t) ∘ (pair-eq-triv s t)) ~ id
issec-pair-eq-triv (dpair x y) (dpair .x .y) refl = refl

is-equiv-eq-pair-triv : {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) → is-equiv (eq-pair-triv s t)
is-equiv-eq-pair-triv s t = pair (dpair (pair-eq-triv s t) (issec-pair-eq-triv s t)) (dpair (pair-eq-triv s t) (isretr-pair-eq-triv s t))

-- Exercises

-- Exercise 5.1
element : {i : Level} {A : UU i} → A → unit → A
element a star = a 

htpy-element-constant : {i : Level} {A : UU i} (a : A) → (element a) ~ (const unit A a)
htpy-element-constant a star = refl

-- Exercise 5.2
ap-const : {i j : Level} {A : UU i} {B : UU j} (b : B) (x y : A) → (ap (const A B b) {x} {y}) ~ const (Id x y) (Id b b) refl
ap-const b x .x refl = refl

-- Exercise 5.3
inv-inv : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

is-equiv-inv : {i : Level} {A : UU i} (x y : A) →
  is-equiv (λ (p : Id x y) → inv p)
is-equiv-inv x y = pair (dpair inv inv-inv) (dpair inv inv-inv)

inv-concat : {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) → (Id x z) → (Id y z)
inv-concat p z q = concat _ (inv p) q

left-inv-inv-concat : {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) → ((inv-concat p z) ∘ (concat y {z} p)) ~ id
left-inv-inv-concat refl z q = refl

right-inv-inv-concat : {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) → ((concat y {z} p) ∘ (inv-concat p z)) ~ id
right-inv-inv-concat refl z refl = refl

is-equiv-concat : {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) → is-equiv (concat y {z} p)
is-equiv-concat p z = pair (dpair (inv-concat p z) (right-inv-inv-concat p z)) (dpair (inv-concat p z) (left-inv-inv-concat p z))

inv-tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} → Id x y → B y → B x
inv-tr B p = tr B (inv p)

left-inv-inv-tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
left-inv-inv-tr B refl b = refl

right-inv-inv-tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
right-inv-inv-tr B refl b = refl

is-equiv-tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → is-equiv (tr B p)
is-equiv-tr B p = pair (dpair (inv-tr B p) (right-inv-inv-tr B p)) (dpair (inv-tr B p) (left-inv-inv-tr B p))

-- Exercise 5.4
is-equiv-htpy : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} →
  f ~ g → is-equiv g → is-equiv f
is-equiv-htpy H (dpair (dpair gs issec) (dpair gr isretr)) =
  pair
    (dpair gs (htpy-concat _ (htpy-right-whisk H gs) issec))
    (dpair gr (htpy-concat (gr ∘ _) (htpy-left-whisk gr H) isretr))

-- Exercise 5.5
section-comp : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → sec h → sec f → sec g
section-comp f g h H (dpair sh sh-issec) (dpair sf sf-issec) = dpair (h ∘ sf) (htpy-concat _ (htpy-inv (htpy-right-whisk H sf)) sf-issec)

section-comp' : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → sec h → sec g → sec f
section-comp' f g h H (dpair sh sh-issec) (dpair sg sg-issec) = dpair (sh ∘ sg) (htpy-concat _ (htpy-right-whisk H (sh ∘ sg)) (htpy-concat _ (htpy-left-whisk g (htpy-right-whisk sh-issec sg)) sg-issec))

retraction-comp : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → retr g → retr f → retr h
retraction-comp f g h H (dpair rg rg-isretr) (dpair rf rf-isretr) = dpair (rf ∘ g) (htpy-concat _ (htpy-left-whisk rf (htpy-inv H)) rf-isretr)

retraction-comp' : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → retr g → retr h → retr f
retraction-comp' f g h H (dpair rg rg-isretr) (dpair rh rh-isretr) = dpair (rh ∘ rg) (htpy-concat _ (htpy-left-whisk (rh ∘ rg) H) (htpy-concat _ (htpy-left-whisk rh (htpy-right-whisk rg-isretr h)) rh-isretr))

is-equiv-comp : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-equiv h → is-equiv g → is-equiv f
is-equiv-comp f g h H (dpair (dpair hs hs-issec) (dpair hr hr-isretr))
  (dpair (dpair gs gs-issec) (dpair gr gr-isretr)) =
  is-equiv-htpy H
    (pair
      (dpair (hs ∘ gs)
        (htpy-concat (g ∘ gs)
          (htpy-left-whisk g (htpy-right-whisk hs-issec gs)) gs-issec))
      (dpair (hr ∘ gr)
        (htpy-concat (hr ∘ h)
          (htpy-left-whisk hr (htpy-right-whisk gr-isretr h)) hr-isretr)))

is-equiv-left-factor : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-equiv f → is-equiv h → is-equiv g
is-equiv-left-factor f g h H
  ( dpair (dpair sf sf-issec) (dpair rf rf-isretr))
  ( dpair (dpair sh sh-issec) (dpair rh rh-isretr)) =
  pair
    ( dpair
      (h ∘ sf)
      (htpy-concat _ (htpy-right-whisk (htpy-inv H) sf) sf-issec))
    ( dpair
      ( h ∘ rf)
      ( htpy-concat _
        ( htpy-left-whisk ((h ∘ rf) ∘ g) (htpy-inv sh-issec))
        ( htpy-concat _
          ( htpy-left-whisk (h ∘ rf) (htpy-right-whisk (htpy-inv H) sh))
          ( htpy-concat _
            ( htpy-left-whisk h (htpy-right-whisk rf-isretr sh))
              sh-issec))))

is-equiv-right-factor : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-equiv g → is-equiv f → is-equiv h
is-equiv-right-factor f g h H
  ( dpair (dpair sg sg-issec) (dpair rg rg-isretr))
  ( dpair (dpair sf sf-issec) (dpair rf rf-isretr)) =
  pair
    ( dpair
      ( sf ∘ g)
      ( htpy-concat (rg ∘ (((g ∘ h) ∘ sf) ∘ g))
        ( htpy-right-whisk (htpy-inv rg-isretr) ((h ∘ sf) ∘ g))
        ( htpy-concat (rg ∘ ((f ∘ sf) ∘ g))
          ( htpy-left-whisk rg (htpy-right-whisk (htpy-inv H) (sf ∘ g)))
          ( htpy-concat (rg ∘ g)
            ( htpy-left-whisk rg (htpy-right-whisk sf-issec g))
             rg-isretr))))
    ( dpair
      ( rf ∘ g)
      ( htpy-concat (rf ∘ f)
        ( htpy-left-whisk rf (htpy-inv H))
          rf-isretr))

-- Exercise 5.6
neg : bool → bool
neg true = false
neg false = true

neg-neg : (neg ∘ neg) ~ id
neg-neg true = refl
neg-neg false = refl

is-equiv-neg : is-equiv neg
is-equiv-neg = pair (dpair neg neg-neg) (dpair neg neg-neg)

not-true-is-false : ¬ (Id true false)
not-true-is-false p =
  ( ind-Id true
    ( λ b p → Eq-𝟚 true b)
    ( reflexive-Eq-𝟚 true)
    false
    p)
    
not-equiv-const : (b : bool) → ¬ (is-equiv (const bool bool b))
not-equiv-const true (dpair (dpair s issec) (dpair r isretr)) =
  not-true-is-false (issec false)
not-equiv-const false (dpair (dpair s issec) (dpair r isretr)) =
  not-true-is-false (inv (issec true))

-- Exercise 5.7

left-inverse-pred-ℤ : (k : ℤ) → Id (pred-ℤ (succ-ℤ k)) k
left-inverse-pred-ℤ (inl zero-ℕ) = refl
left-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
left-inverse-pred-ℤ (inr (inl star)) = refl
left-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
left-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl

right-inverse-pred-ℤ : (k : ℤ) → Id (succ-ℤ (pred-ℤ k)) k
right-inverse-pred-ℤ (inl zero-ℕ) = refl
right-inverse-pred-ℤ (inl (succ-ℕ x)) = refl
right-inverse-pred-ℤ (inr (inl star)) = refl
right-inverse-pred-ℤ (inr (inr zero-ℕ)) = refl
right-inverse-pred-ℤ (inr (inr (succ-ℕ x))) = refl

is-equiv-succ-ℤ : is-equiv succ-ℤ
is-equiv-succ-ℤ =
  pair
  ( dpair pred-ℤ right-inverse-pred-ℤ)
  ( dpair pred-ℤ left-inverse-pred-ℤ)

-- Exercise 5.8
swap-coprod : {i j : Level} (A : UU i) (B : UU j) → coprod A B → coprod B A
swap-coprod A B (inl x) = inr x
swap-coprod A B (inr x) = inl x

swap-swap-coprod : {i j : Level} (A : UU i) (B : UU j) → ((swap-coprod B A) ∘ (swap-coprod A B)) ~ id
swap-swap-coprod A B (inl x) = refl
swap-swap-coprod A B (inr x) = refl

is-equiv-swap-coprod : {i j : Level} (A : UU i) (B : UU j) → is-equiv (swap-coprod A B)
is-equiv-swap-coprod A B = pair (dpair (swap-coprod B A) (swap-swap-coprod B A)) (dpair (swap-coprod B A) (swap-swap-coprod A B))

swap-prod : {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B (dpair x y) = dpair y x

swap-swap-prod : {i j : Level} (A : UU i) (B : UU j) → ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (dpair x y) = refl

is-equiv-swap-prod : {i j : Level} (A : UU i) (B : UU j) → is-equiv (swap-prod A B)
is-equiv-swap-prod A B = pair (dpair (swap-prod B A) (swap-swap-prod B A)) (dpair (swap-prod B A) (swap-swap-prod A B))

-- Exercise 5.9
ap-retraction : {i j : Level} {A : UU i} {B : UU j} (i : A → B) (r : B → A) (H : (r ∘ i) ~ id) (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p = concat (r (i x)) (inv (H x)) (concat (r (i y)) (ap r p) (H y))

isretr-ap-retraction : {i j : Level} {A : UU i} {B : UU j} (i : A → B) (r : B → A) (H : (r ∘ i) ~ id) (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap : {i j : Level} {A : UU i} {B : UU j} (i : A → B) (r : B → A) (H : (r ∘ i) ~ id) (x y : A) → retr (ap i {x} {y})
retr-ap i r H x y = dpair (ap-retraction i r H x y) (isretr-ap-retraction i r H x y)

-- Exercise 5.10
Σ-assoc : {i j k : Level} (A : UU i) (B : A → UU j) (C : (x : A) → B x → UU k) → Σ (Σ A B) (ind-Σ C) → Σ A (λ x → Σ (B x) (C x))
Σ-assoc A B C (dpair (dpair x y) z) = dpair x (dpair y z)

Σ-assoc' : {i j k : Level} (A : UU i) (B : A → UU j) (C : (x : A) → B x → UU k) → Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (ind-Σ C)
Σ-assoc' A B C (dpair x (dpair y z)) = dpair (dpair x y) z

Σ-assoc-assoc : {i j k : Level} (A : UU i) (B : A → UU j) (C : (x : A) → B x → UU k) → ((Σ-assoc' A B C) ∘ (Σ-assoc A B C)) ~ id
Σ-assoc-assoc A B C (dpair (dpair x y) z) = refl

Σ-assoc-assoc' : {i j k : Level} (A : UU i) (B : A → UU j) (C : (x : A) → B x → UU k) → ((Σ-assoc A B C) ∘ (Σ-assoc' A B C)) ~ id
Σ-assoc-assoc' A B C (dpair x (dpair y z)) = refl

is-equiv-Σ-assoc : {i j k : Level} (A : UU i) (B : A → UU j) (C : (x : A) → B x → UU k) → is-equiv (Σ-assoc A B C)
is-equiv-Σ-assoc A B C = pair (dpair (Σ-assoc' A B C) (Σ-assoc-assoc' A B C)) (dpair (Σ-assoc' A B C) (Σ-assoc-assoc A B C))

-- Exercise 5.11
Σ-swap : {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) → Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
Σ-swap A B C (dpair x (dpair y z)) = dpair y (dpair x z)

Σ-swap' : {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) → Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
Σ-swap' A B C = Σ-swap B A (λ y x → C x y)

Σ-swap-swap : {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) → ((Σ-swap' A B C) ∘ (Σ-swap A B C)) ~ id
Σ-swap-swap A B C (dpair x (dpair y z)) = refl

is-equiv-Σ-swap : {i j k : Level} (A : UU i) (B : UU j) (C : A → B → UU k) → is-equiv (Σ-swap A B C)
is-equiv-Σ-swap A B C = pair (dpair (Σ-swap' A B C) (Σ-swap-swap B A (λ y x → C x y))) (dpair (Σ-swap' A B C) (Σ-swap-swap A B C))

-- Exercise 5.12

-- First we construct directly some identifications on the type of integers.

left-unit-law-add-ℤ : (k : ℤ) → Id (add-ℤ zero-ℤ k) k
left-unit-law-add-ℤ k = refl

right-unit-law-add-ℤ : (k : ℤ) → Id (add-ℤ k zero-ℤ) k
right-unit-law-add-ℤ (inl zero-ℕ) = refl
right-unit-law-add-ℤ (inl (succ-ℕ x)) = ap pred-ℤ (right-unit-law-add-ℤ (inl x))
right-unit-law-add-ℤ (inr (inl star)) = refl
right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) = ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))

left-predecessor-law-add-ℤ : (x y : ℤ) → Id (add-ℤ (pred-ℤ x) y) (pred-ℤ (add-ℤ x y))
left-predecessor-law-add-ℤ (inl n) y = refl
left-predecessor-law-add-ℤ (inr (inl star)) y = refl
left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y = concat y (ap (λ t → add-ℤ t y) (left-inverse-pred-ℤ zero-ℤ)) (inv (left-inverse-pred-ℤ y))
left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y = concat (add-ℤ (inr (inr x)) y) (ap (λ t → (add-ℤ t y)) (left-inverse-pred-ℤ (inr (inr x)))) (inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) y)))

right-predecessor-law-add-ℤ : (x y : ℤ) → Id (add-ℤ x (pred-ℤ y)) (pred-ℤ (add-ℤ x y))
right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n = ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
right-predecessor-law-add-ℤ (inr (inl star)) n = refl
right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n = concat n (right-inverse-pred-ℤ n) (inv (left-inverse-pred-ℤ n))
right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n = concat (succ-ℤ (pred-ℤ (add-ℤ (inr (inr x)) n))) (ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)) (concat (add-ℤ (inr (inr x)) n) (right-inverse-pred-ℤ (add-ℤ (inr (inr x)) n)) (inv (left-inverse-pred-ℤ (add-ℤ (inr (inr x)) n))))

left-successor-law-add-ℤ : (x y : ℤ) → Id (add-ℤ (succ-ℤ x) y) (succ-ℤ (add-ℤ x y))
left-successor-law-add-ℤ (inl zero-ℕ) y = concat y (ap (λ t → add-ℤ t y) (right-inverse-pred-ℤ zero-ℤ)) (inv (right-inverse-pred-ℤ y))
left-successor-law-add-ℤ (inl (succ-ℕ x)) y = concat (succ-ℤ (pred-ℤ (add-ℤ (inl x) y))) (inv (right-inverse-pred-ℤ (add-ℤ (inl x) y))) (ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y)))
left-successor-law-add-ℤ (inr (inl star)) y = refl
left-successor-law-add-ℤ (inr (inr x)) y = refl

associative-add-ℤ : (x y z : ℤ) → Id (add-ℤ (add-ℤ x y) z) (add-ℤ x (add-ℤ y z))
associative-add-ℤ (inl zero-ℕ) y z =
  concat
    ( add-ℤ (pred-ℤ y) z)
    ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ zero-ℤ y))
    ( concat
      ( pred-ℤ (add-ℤ y z))
      ( left-predecessor-law-add-ℤ y z)
      ( inv (left-predecessor-law-add-ℤ zero-ℤ (add-ℤ y z))))
associative-add-ℤ (inl (succ-ℕ x)) y z =
  concat
    ( add-ℤ (pred-ℤ (add-ℤ (inl x) y)) z)
    ( ap (λ t → add-ℤ t z) (left-predecessor-law-add-ℤ (inl x) y))
    ( concat
      ( pred-ℤ (add-ℤ (add-ℤ (inl x) y) z))
      ( left-predecessor-law-add-ℤ (add-ℤ (inl x) y) z)
      ( concat
        ( pred-ℤ (add-ℤ (inl x) (add-ℤ y z)))
        ( ap pred-ℤ (associative-add-ℤ (inl x) y z))
        ( inv (left-predecessor-law-add-ℤ (inl x) (add-ℤ y z)))))
associative-add-ℤ (inr (inl star)) y z = refl
associative-add-ℤ (inr (inr zero-ℕ)) y z =
  concat
    ( add-ℤ (succ-ℤ y) z)
    ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ zero-ℤ y))
    ( concat
      ( succ-ℤ (add-ℤ y z))
      ( left-successor-law-add-ℤ y z)
      ( inv (left-successor-law-add-ℤ zero-ℤ (add-ℤ y z))))
associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
  concat
    ( add-ℤ (succ-ℤ (add-ℤ (inr (inr x)) y)) z)
    ( ap (λ t → add-ℤ t z) (left-successor-law-add-ℤ (inr (inr x)) y))
    ( concat
      ( succ-ℤ (add-ℤ (add-ℤ (inr (inr x)) y) z))
      ( left-successor-law-add-ℤ (add-ℤ (inr (inr x)) y) z)
      ( concat
        ( succ-ℤ (add-ℤ (inr (inr x)) (add-ℤ y z)))
        ( ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z))
        ( inv (left-successor-law-add-ℤ (inr (inr x)) (add-ℤ y z)))))

right-successor-law-add-ℤ : (x y : ℤ) → Id (add-ℤ x (succ-ℤ y)) (succ-ℤ (add-ℤ x y))
right-successor-law-add-ℤ x y = {!!}

{-
-- Next, we equip the type ℕ × ℕ with the structure of a monoid.

add-ℕℕ : prod ℕ ℕ → prod ℕ ℕ → prod ℕ ℕ
add-ℕℕ (dpair m n) (dpair m' n') = dpair (add-ℕ m m') (add-ℕ n n')

zero-ℕℕ : prod ℕ ℕ
zero-ℕℕ = pair zero-ℕ zero-ℕ

left-unit-law-add-ℕℕ : (x : prod ℕ ℕ) → Id (add-ℕℕ zero-ℕℕ x) x
left-unit-law-add-ℕℕ (dpair m n) = eq-pair (dpair refl refl)

right-unit-law-add-ℕℕ : (x : prod ℕ ℕ) → Id (add-ℕℕ x zero-ℕℕ) x
right-unit-law-add-ℕℕ (dpair m n) = eq-pair-triv _ _ (pair (right-unit-law-add-ℕ m) (right-unit-law-add-ℕ n))

associative-add-ℕℕ : (x y z : prod ℕ ℕ) → Id (add-ℕℕ (add-ℕℕ x y) z) (add-ℕℕ x (add-ℕℕ y z))
associative-add-ℕℕ (dpair m n) (dpair m' n') (dpair m'' n'') = eq-pair-triv _ _ (pair (associative-add-ℕ m m' m'') (associative-add-ℕ n n' n''))

-- We equip the type ℕ × ℕ with some further useful structure. There is a pointwise multiplication structure on ℕ × ℕ, of which the unit is (pair one-ℕ one-ℕ). This is, however, not the multiplication we will be looking at. There is a second multiplication structure on ℕ × ℕ, of which the unit is (pair one-ℕ zero-ℕ). 

one-ℕℕ : prod ℕ ℕ
one-ℕℕ = pair one-ℕ zero-ℕ

mul-ℕℕ : prod ℕ ℕ → prod ℕ ℕ → prod ℕ ℕ
mul-ℕℕ (dpair m n) (dpair m' n') = dpair (add-ℕ (mul-ℕ m m') (mul-ℕ n n')) (add-ℕ (mul-ℕ m n') (mul-ℕ n m'))

-- We note that this multiplication is also associative, satisfies the unit laws, is commutative, and multiplication distributes over pointwise addition. The proof term for associativity is, however, rather long.

succ-ℕℕ : prod ℕ ℕ → prod ℕ ℕ
succ-ℕℕ (dpair m n) = pair (succ-ℕ m) n

pred-ℕℕ : prod ℕ ℕ → prod ℕ ℕ
pred-ℕℕ (dpair m n) = dpair m (succ-ℕ n)

diagonal-step-ℕℕ : prod ℕ ℕ → prod ℕ ℕ
diagonal-step-ℕℕ (dpair m n) = dpair (succ-ℕ m) (succ-ℕ n)

right-diagonal-step-law-add-ℕℕ : (x y : prod ℕ ℕ) → Id (add-ℕℕ x (diagonal-step-ℕℕ y)) (diagonal-step-ℕℕ (add-ℕℕ x y))
right-diagonal-step-law-add-ℕℕ (dpair m n) (dpair m' n') = eq-pair-triv _ _ (pair (right-successor-law-add-ℕ m m') (right-successor-law-add-ℕ n n'))

-- Now we establish that the type ℤ is a retract of the type ℕ × ℕ

ℤ-in-ℕℕ : ℤ → prod ℕ ℕ
ℤ-in-ℕℕ (inl x) = pair zero-ℕ (succ-ℕ x)
ℤ-in-ℕℕ (inr (inl x)) = pair zero-ℕ zero-ℕ
ℤ-in-ℕℕ (inr (inr x)) = pair (succ-ℕ x) zero-ℕ

ℕℕ-to-ℤ : prod ℕ ℕ → ℤ
ℕℕ-to-ℤ (dpair zero-ℕ zero-ℕ) = zero-ℤ
ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ m)) = in-neg m
ℕℕ-to-ℤ (dpair (succ-ℕ n) zero-ℕ) = in-pos n
ℕℕ-to-ℤ (dpair (succ-ℕ n) (succ-ℕ m)) = ℕℕ-to-ℤ (dpair n m)

is-retraction-ℕℕ-to-ℤ : (k : ℤ) → Id (ℕℕ-to-ℤ (ℤ-in-ℕℕ k)) k
is-retraction-ℕℕ-to-ℤ (inl x) = refl
is-retraction-ℕℕ-to-ℤ (inr (inl star)) = refl
is-retraction-ℕℕ-to-ℤ (inr (inr x)) = refl

-- similarly, we have a map from ℕ × ℕ to ℕ × ℕ that does the same thing:

ℕℕ-to-ℕℕ : prod ℕ ℕ → prod ℕ ℕ
ℕℕ-to-ℕℕ (dpair zero-ℕ n) = dpair zero-ℕ n
ℕℕ-to-ℕℕ (dpair (succ-ℕ m) zero-ℕ) = dpair (succ-ℕ m) zero-ℕ
ℕℕ-to-ℕℕ (dpair (succ-ℕ m) (succ-ℕ n)) = ℕℕ-to-ℕℕ (dpair m n)

idempotent-ℕℕ-to-ℕℕ : (x : prod ℕ ℕ) → Id (ℕℕ-to-ℕℕ (ℕℕ-to-ℕℕ x)) (ℕℕ-to-ℕℕ x)
idempotent-ℕℕ-to-ℕℕ (dpair zero-ℕ n) = refl
idempotent-ℕℕ-to-ℕℕ (dpair (succ-ℕ m) zero-ℕ) = refl 
idempotent-ℕℕ-to-ℕℕ (dpair (succ-ℕ m) (succ-ℕ n)) = idempotent-ℕℕ-to-ℕℕ (dpair m n)

preserves-diagonal-step-ℕℕ-to-ℕℕ : (x : prod ℕ ℕ) → Id (ℕℕ-to-ℕℕ (diagonal-step-ℕℕ x)) (ℕℕ-to-ℕℕ x)
preserves-diagonal-step-ℕℕ-to-ℕℕ (dpair m n) = refl

preserves-addition-ℕℕ-to-ℕℕ : (x y : prod ℕ ℕ) → Id (ℕℕ-to-ℕℕ (add-ℕℕ x y)) (ℕℕ-to-ℕℕ (add-ℕℕ (ℕℕ-to-ℕℕ x) (ℕℕ-to-ℕℕ y)))
preserves-addition-ℕℕ-to-ℕℕ (dpair zero-ℕ zero-ℕ) (dpair m' n') =
  concat (ℕℕ-to-ℕℕ (ℕℕ-to-ℕℕ (dpair m' n')))
  ( inv (idempotent-ℕℕ-to-ℕℕ (dpair m' n')))
  ( ap ℕℕ-to-ℕℕ (inv (left-unit-law-add-ℕℕ (ℕℕ-to-ℕℕ (dpair m' n')))))
preserves-addition-ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair zero-ℕ n') = refl
preserves-addition-ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair (succ-ℕ m') zero-ℕ) = refl
preserves-addition-ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair (succ-ℕ m') (succ-ℕ n')) =
  concat
    ( ℕℕ-to-ℕℕ
      ( ℕℕ-to-ℕℕ
        ( add-ℕℕ
          ( dpair zero-ℕ (succ-ℕ n))
          ( dpair (succ-ℕ m') (succ-ℕ n')))))
    ( inv
      ( idempotent-ℕℕ-to-ℕℕ
        ( add-ℕℕ
          ( dpair zero-ℕ (succ-ℕ n))
          ( dpair (succ-ℕ m') (succ-ℕ n')))))
    ( concat
      ( ℕℕ-to-ℕℕ (ℕℕ-to-ℕℕ (diagonal-step-ℕℕ (add-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair m' n')))))
      ( ap (ℕℕ-to-ℕℕ ∘ ℕℕ-to-ℕℕ) (right-diagonal-step-law-add-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair m' n')))
      ( concat
        ( ℕℕ-to-ℕℕ (ℕℕ-to-ℕℕ (add-ℕℕ (ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n))) (ℕℕ-to-ℕℕ (dpair m' n')))))
        ( ap ℕℕ-to-ℕℕ (preserves-addition-ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n)) (dpair m' n')))
        ( idempotent-ℕℕ-to-ℕℕ (add-ℕℕ (ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n))) (ℕℕ-to-ℕℕ (dpair m' n'))))))

ℕℕ-to-ℤ-ℕℕ-to-ℕℕ : (x : prod ℕ ℕ) → Id (ℕℕ-to-ℤ (ℕℕ-to-ℕℕ x)) (ℕℕ-to-ℤ x)
ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (dpair zero-ℕ zero-ℕ) = refl
ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (dpair zero-ℕ (succ-ℕ n)) = refl
ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (dpair (succ-ℕ m) zero-ℕ) = refl
ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (dpair (succ-ℕ m) (succ-ℕ n)) = ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (dpair m n)

predecessor-law-ℕℕ-to-ℤ : (x : prod ℕ ℕ) → Id (ℕℕ-to-ℤ (pred-ℕℕ x)) (pred-ℤ (ℕℕ-to-ℤ x))
predecessor-law-ℕℕ-to-ℤ (dpair zero-ℕ zero-ℕ) = refl
predecessor-law-ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ n)) = refl
predecessor-law-ℕℕ-to-ℤ (dpair (succ-ℕ zero-ℕ) zero-ℕ) = refl
predecessor-law-ℕℕ-to-ℤ (dpair (succ-ℕ (succ-ℕ m)) zero-ℕ) = refl
predecessor-law-ℕℕ-to-ℤ (dpair (succ-ℕ m) (succ-ℕ n)) = predecessor-law-ℕℕ-to-ℤ (dpair m n)

preserves-addition-ℕℕ-to-ℤ' : (x y : prod ℕ ℕ) → Id (ℕℕ-to-ℤ (add-ℕℕ (ℕℕ-to-ℕℕ x) (ℕℕ-to-ℕℕ y))) (add-ℤ (ℕℕ-to-ℤ x) (ℕℕ-to-ℤ y))
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ zero-ℕ) (dpair zero-ℕ zero-ℕ) = refl
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ zero-ℕ) (dpair zero-ℕ (succ-ℕ n')) = refl
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ zero-ℕ) (dpair (succ-ℕ m') zero-ℕ) = refl
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ zero-ℕ) (dpair (succ-ℕ m') (succ-ℕ n')) = preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ zero-ℕ) (dpair m' n')
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ (succ-ℕ n)) (dpair zero-ℕ zero-ℕ) =
  concat
    ( ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ n)))
    ( ap ℕℕ-to-ℤ
      ( eq-pair-triv
        ( dpair zero-ℕ (add-ℕ (succ-ℕ n) zero-ℕ))
        ( dpair zero-ℕ (succ-ℕ n))
        ( pair refl (right-unit-law-add-ℕ (succ-ℕ n)))))
    ( inv (right-unit-law-add-ℤ (ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ n)))))
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ (succ-ℕ n)) (dpair zero-ℕ (succ-ℕ n')) = concat (ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ (add-ℕ (succ-ℕ n) n')))) (ap ℕℕ-to-ℤ (eq-pair-triv (dpair zero-ℕ (add-ℕ (succ-ℕ n) (succ-ℕ n'))) (dpair zero-ℕ (succ-ℕ (add-ℕ (succ-ℕ n) n'))) (pair refl (right-successor-law-add-ℕ (succ-ℕ n) n')))) (concat (pred-ℤ (ℕℕ-to-ℤ (dpair zero-ℕ (add-ℕ (succ-ℕ n) n')))) (predecessor-law-ℕℕ-to-ℤ (dpair zero-ℕ (add-ℕ (succ-ℕ n) n'))) (concat (pred-ℤ (add-ℤ (ℕℕ-to-ℤ (dpair zero-ℕ (succ-ℕ n))) (ℕℕ-to-ℤ (dpair zero-ℕ n')))) (ap pred-ℤ (preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ (succ-ℕ n)) (dpair zero-ℕ n'))) {!!}))
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ (succ-ℕ n)) (dpair (succ-ℕ m') zero-ℕ) = {!refl!}
preserves-addition-ℕℕ-to-ℤ' (dpair zero-ℕ (succ-ℕ n)) (dpair (succ-ℕ m') (succ-ℕ n')) = {!refl!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) zero-ℕ) (dpair zero-ℕ zero-ℕ) = {!refl!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) zero-ℕ) (dpair zero-ℕ (succ-ℕ n')) = {!refl!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) zero-ℕ) (dpair (succ-ℕ m') zero-ℕ) = {!!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) zero-ℕ) (dpair (succ-ℕ m') (succ-ℕ n')) = {!!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) (succ-ℕ n)) (dpair zero-ℕ zero-ℕ) = {!!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) (succ-ℕ n)) (dpair zero-ℕ (succ-ℕ n')) = {!!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) (succ-ℕ n)) (dpair (succ-ℕ m') zero-ℕ) = {!!}
preserves-addition-ℕℕ-to-ℤ' (dpair (succ-ℕ m) (succ-ℕ n)) (dpair (succ-ℕ m') (succ-ℕ n')) = {!!}

preserves-addition-ℕℕ-to-ℤ : (x y : prod ℕ ℕ) → Id (ℕℕ-to-ℤ (add-ℕℕ x y)) (add-ℤ (ℕℕ-to-ℤ x) (ℕℕ-to-ℤ y))
preserves-addition-ℕℕ-to-ℤ x y = concat (ℕℕ-to-ℤ (ℕℕ-to-ℕℕ (add-ℕℕ x y))) (inv (ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (add-ℕℕ x y))) (concat (ℕℕ-to-ℤ (ℕℕ-to-ℕℕ (add-ℕℕ (ℕℕ-to-ℕℕ x) (ℕℕ-to-ℕℕ y)))) (ap ℕℕ-to-ℤ (preserves-addition-ℕℕ-to-ℕℕ x y)) (concat (ℕℕ-to-ℤ (add-ℕℕ (ℕℕ-to-ℕℕ x) (ℕℕ-to-ℕℕ y))) (ℕℕ-to-ℤ-ℕℕ-to-ℕℕ (add-ℕℕ (ℕℕ-to-ℕℕ x) (ℕℕ-to-ℕℕ y))) {!!}) )


{-
associative-mul-ℕℕ : (x y z : prod ℕ ℕ) → Id (mul-ℕℕ (mul-ℕℕ x y) z) (mul-ℕℕ x (mul-ℕℕ y z))
associative-mul-ℕℕ (dpair m n) (dpair m' n') (dpair m'' n'') =
  eq-pair-triv
    ( pair
      ( add-ℕ
        ( mul-ℕ (add-ℕ (mul-ℕ m m') (mul-ℕ n n')) m'')
        ( mul-ℕ (add-ℕ (mul-ℕ m n') (mul-ℕ n m')) n''))
      ( add-ℕ
        ( mul-ℕ (add-ℕ (mul-ℕ m m') (mul-ℕ n n')) n'')
        ( mul-ℕ (add-ℕ (mul-ℕ m n') (mul-ℕ n m')) m'')))
    ( pair
      ( add-ℕ
        ( mul-ℕ m (add-ℕ (mul-ℕ m' m'') (mul-ℕ n' n'')))
        ( mul-ℕ n (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m''))))
      ( add-ℕ
        ( mul-ℕ m (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m'')))
        ( mul-ℕ n (add-ℕ (mul-ℕ m' m'') (mul-ℕ n' n'')))))
    ( pair
      ( concat
        ( add-ℕ
          ( add-ℕ
            ( mul-ℕ (mul-ℕ m m') m'')
            ( mul-ℕ (mul-ℕ n n') m''))
          ( mul-ℕ (add-ℕ (mul-ℕ m n') (mul-ℕ n m')) n''))
        ( ap
          ( λ t → add-ℕ t (mul-ℕ (add-ℕ (mul-ℕ m n') (mul-ℕ n m')) n''))
          ( right-distributive-mul-add-ℕ (mul-ℕ m m') (mul-ℕ n n') m''))
        ( concat
          ( add-ℕ
            ( add-ℕ
              ( mul-ℕ (mul-ℕ m m') m'')
              ( mul-ℕ (mul-ℕ n n') m''))
            ( add-ℕ
              ( mul-ℕ (mul-ℕ m n') n'')
              ( mul-ℕ (mul-ℕ n m') n'')))
          ( ap
            ( λ t → add-ℕ
              ( add-ℕ (mul-ℕ (mul-ℕ m m') m'') (mul-ℕ (mul-ℕ n n') m'')) t)
            ( right-distributive-mul-add-ℕ (mul-ℕ m n') (mul-ℕ n m') n''))
          ( concat
            ( add-ℕ
              ( mul-ℕ (mul-ℕ m m') m'')
              ( add-ℕ
                ( mul-ℕ (mul-ℕ n n') m'')
                ( add-ℕ
                  ( mul-ℕ (mul-ℕ m n') n'')
                  ( mul-ℕ (mul-ℕ n m') n''))))
            ( associative-add-ℕ
              ( mul-ℕ (mul-ℕ m m') m'')
              ( mul-ℕ (mul-ℕ n n') m'')
              ( add-ℕ
                  ( mul-ℕ (mul-ℕ m n') n'')
                  ( mul-ℕ (mul-ℕ n m') n'')))
            ( concat
              ( add-ℕ
                ( mul-ℕ m (mul-ℕ m' m''))
                ( add-ℕ
                  ( mul-ℕ (mul-ℕ n n') m'')
                  ( add-ℕ
                    ( mul-ℕ (mul-ℕ m n') n'')
                    ( mul-ℕ (mul-ℕ n m') n''))))
              ( ap
                ( λ t → add-ℕ t
                  ( add-ℕ
                    ( mul-ℕ (mul-ℕ n n') m'')
                    ( add-ℕ
                      ( mul-ℕ (mul-ℕ m n') n'')
                      ( mul-ℕ (mul-ℕ n m') n''))))
                ( associative-mul-ℕ m m' m''))
              ( concat
                ( add-ℕ
                  ( add-ℕ
                    ( mul-ℕ m (mul-ℕ m' m''))
                    ( mul-ℕ m (mul-ℕ n' n'')))
                  ( mul-ℕ n (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m''))))
                ( concat
                  ( add-ℕ
                    ( mul-ℕ m (mul-ℕ m' m''))
                    ( add-ℕ
                      ( mul-ℕ m (mul-ℕ n' n''))
                      ( mul-ℕ n (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m'')))))
                  ( ap
                    ( λ t → add-ℕ (mul-ℕ m (mul-ℕ m' m'')) t)
                    ( concat
                      ( add-ℕ
                        ( mul-ℕ m (mul-ℕ n' n''))
                        ( add-ℕ
                          ( mul-ℕ n (mul-ℕ m' n''))
                          ( mul-ℕ n (mul-ℕ n' m''))))
                      ( concat
                        ( add-ℕ
                          ( add-ℕ
                            ( mul-ℕ n (mul-ℕ m' n''))
                            ( mul-ℕ n (mul-ℕ n' m'')))
                          ( mul-ℕ m (mul-ℕ n' n'')))
                        ( concat
                          ( add-ℕ
                            ( add-ℕ
                              ( mul-ℕ (mul-ℕ n m') n'')
                              ( mul-ℕ n (mul-ℕ n' m'')))
                            ( mul-ℕ m (mul-ℕ n' n'')))
                          {!!}
                          ( ap
                            ( λ t → add-ℕ
                              ( add-ℕ t ( mul-ℕ n (mul-ℕ n' m'')))
                              ( mul-ℕ m (mul-ℕ n' n'')))
                            ( associative-mul-ℕ n m' n'')))
                          {!!})
                      ( inv
                        ( ap
                          ( λ t → add-ℕ (mul-ℕ m (mul-ℕ n' n'')) t)
                          ( left-distributive-mul-add-ℕ
                            n
                            (mul-ℕ m' n'')
                            (mul-ℕ n' m''))))))
                  ( inv
                    ( associative-add-ℕ
                      ( mul-ℕ m (mul-ℕ m' m''))
                      ( mul-ℕ m (mul-ℕ n' n''))
                      ( mul-ℕ n (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m''))))))
                ( ap
                  ( λ t → add-ℕ t
                    ( mul-ℕ n (add-ℕ (mul-ℕ m' n'') (mul-ℕ n' m''))))
                  ( inv
                    ( left-distributive-mul-add-ℕ
                      m
                      (mul-ℕ m' m'')
                      (mul-ℕ n' n'')))))))))
      {!!})
-}
-}

\end{code}
