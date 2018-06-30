\begin{code}

{-# OPTIONS --without-K #-}

module Lecture5 where

open import Lecture4 public

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

-- this equivalence symbol is \simeq
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

-- Exercises below






































-- Exercise 5.1

-- singleton-ind-const-htpy : {i : Level} {A : UU i} (a : A) → ((ind-unit {i} {const unit (UU i) A} a) ~ (const unit A a))
-- singleton-ind-const-htpy a = \ x → (a == a)

-- Exercise 5.2
ap-const-is-const-refl : {i j : Level} {A : UU i} {B : UU j} (b : B) {x y : A} → (ap (const A B b)) ~ (const (Id x y) (Id b b) refl)
ap-const-is-const-refl b refl = refl

-- Exercise 5.3
inv-inv-htpy : {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv-htpy refl = refl

is-equiv-inv : {i : Level} {A : UU i} (x y : A) →
  is-equiv (λ (p : Id x y) → inv p)
is-equiv-inv x y = pair (dpair inv inv-inv-htpy) (dpair inv inv-inv-htpy)

concat-inv-left-htpy : {i : Level} {A : UU i} {x y z : A} (p : Id x y) → (q : Id y z) → Id ((inv p) · (p · q)) q
concat-inv-left-htpy refl q = refl

concat-inv-right-htpy : {i : Level} {A : UU i} {x y z : A} (p : Id x y) → (r : Id x z) → Id (p · ((inv p) · r)) r
concat-inv-right-htpy refl r = refl

is-equiv-concat : {i : Level} {A : UU i} (x y z : A) (p : Id x y) → (is-equiv λ (q : Id y z) → p · q)
is-equiv-concat x y z p = pair (dpair (λ (r : Id x z) → ((inv p) · r)) (λ (r : Id x z) → concat-inv-right-htpy p r)) (dpair (λ (r : Id x z) → (inv p) · r) (λ (q : Id y z) → concat-inv-left-htpy p q))

tr-inv-htpy : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B x) → Id (tr B (inv p) (tr B p b)) b
tr-inv-htpy refl b = refl

tr-inv-htpy' : {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y) (b : B y) → Id (tr B p (tr B (inv p) b)) b
tr-inv-htpy' refl b = refl

is-equiv-tr : {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → is-equiv (λ b → (tr B p b))
is-equiv-tr B p = pair (dpair (tr B (inv p)) (tr-inv-htpy' p)) (dpair (tr B (inv p)) (tr-inv-htpy p))

-- Exercise 5.4
is-equiv-htpy : {i j : Level} {A : UU i} {B : UU j} {f g : A → B} →
  f ~ g → is-equiv g → is-equiv f
is-equiv-htpy H (dpair (dpair gs issec) (dpair gr isretr)) =
  pair
    (dpair gs (htpy-concat _ (htpy-right-whisk H gs) issec))
    (dpair gr (htpy-concat (gr ∘ _) (htpy-left-whisk gr H) isretr))

-- Exercise 5.5
is-equiv-comp : {i j k : Level} {A : UU i} {B : UU j} {X : UU k} {f : A → X} {g : B → X} {h : A → B} (H : f ~ (g ∘ h)) → is-equiv h → is-equiv g → is-equiv f
is-equiv-comp {i} {j} {k} {A} {B} {X} {f} {g} {h} H (dpair (dpair hs hs-issec) (dpair hr hr-isretr))
  (dpair (dpair gs gs-issec) (dpair gr gr-isretr)) =
  is-equiv-htpy H
    (pair
      (dpair (hs ∘ gs)
        (htpy-concat (g ∘ gs)
          (htpy-left-whisk g (htpy-right-whisk hs-issec gs)) gs-issec))
      (dpair (hr ∘ gr)
        (htpy-concat (hr ∘ h)
          (htpy-left-whisk hr (htpy-right-whisk gr-isretr h)) hr-isretr)))

-- Exercise 5.6
-- is-equiv-not : is-equiv not
-- is-equiv-not not = pair (dpair not (λ (x : bool) → refl)) (dpair not (λ (x : bool) → refl))

-- Exercise 5.7
-- Exercise 5.8
-- construct equivalences A + B <-> B + A and A x B <-> B x A
coprod-rev : {i j : Level} (A : UU i) (B : UU j) → (coprod A B) → (coprod B A)
coprod-rev A B (inl a) = inr a
coprod-rev A B (inr b) = inl b

coprod-rev-squared-is-id : {i j : Level} (A : UU i) (B : UU j) → (coprod-rev B A ∘ coprod-rev A B) ~ id
coprod-rev-squared-is-id A B (inl a) = refl
coprod-rev-squared-is-id A B (inr b) = refl

is-equiv-coprod-rev : {i j : Level} (A : UU i) (B : UU j) → is-equiv (coprod-rev A B)
is-equiv-coprod-rev A B = dpair (dpair (coprod-rev B A) (coprod-rev-squared-is-id B A)) (dpair (coprod-rev B A) (coprod-rev-squared-is-id A B))

prod-rev : {i j : Level} (A : UU i) (B : UU j) → (prod A B) → (prod B A)
prod-rev A B x = pair (pr2 x) (pr1 x)

prod-rev-squared-is-id : {i j : Level} (A : UU i) (B : UU j) → (prod-rev B A ∘ prod-rev A B) ~ id
prod-rev-squared-is-id A B (dpair a b) = refl

is-equiv-prod-rev : {i j : Level} (A : UU i) (B : UU j) → is-equiv (prod-rev A B)
is-equiv-prod-rev A B = dpair (dpair (prod-rev B A) (prod-rev-squared-is-id B A)) (dpair (prod-rev B A) (prod-rev-squared-is-id A B))

-- Exercise 5.9
--                             i      r
-- Consider a sec/retr pair A ---> B ---> A with H : r ∘ i ~ id. Show that x = y is a retr of i(x) = i(y)
path-is-retr-of-apsec : {i j : Level} {A : UU i} {B : UU j} (x : A) (y : B) → (i : A → B) → sec i → (r : B → A) → retr r → ((r ∘ i) ~ id) → (Id (i x) (i y)) → (Id x y)
path-is-retr-of-apsec x y i i-is-sec r r-is-retr H p = (x)
  ==⟨ (inv (H x)) ⟩
(r (i x))
  ==⟨ (inv (ap r)) ⟩
(i x)
  ==⟨ p ⟩
(i y)
  ==⟨ inv (ap i) ⟩
(y)
  ==∎

-- Exercise 5.10
-- Exercise 5.11
-- Exercise 5.12
-- Exercise 5.13

\end{code}
