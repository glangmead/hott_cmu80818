\begin{code}

{-# OPTIONS --without-K #-}

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
    ( λ b p → Eq2 true b)
    ( reflexive-Eq2 true)
    false
    p)
    
not-equiv-const : (b : bool) → ¬ (is-equiv (const bool bool b))
not-equiv-const true (dpair (dpair s issec) (dpair r isretr)) =
  not-true-is-false (issec false)
not-equiv-const false (dpair (dpair s issec) (dpair r isretr)) =
  not-true-is-false (inv (issec true))

\end{code}
