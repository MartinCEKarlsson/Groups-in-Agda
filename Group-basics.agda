{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences
open import Eq-reasoning
open import SetsAndProps

{- This file draws heavily from the HOTT-library -}
{- In this file we have the basic definitions of groups, subgroups, normal subgroups, and group homomorphisms + basic lemma's -}
{- PLEASE ONLY PUSH THIS FILE IF IT LOADS WITHOUT OPEN GOALS, OTHERWISE THE OTHER FILES WILL NOT LOAD -}

module Group-basics where

{- Definition of the properties that a group has, and some useful lemma's -}
record is-group {ℓ} (X : Set ℓ) : Set ℓ where
  field
    {-
    A group G is an algebra hG; ·; −1; 1i with a binary, a unary, and
    nullary operation in which the following identities are true:
    G1: x · (y · z) ≈ (x · y) · z
    G2: x · 1 ≈ 1 · x ≈ x
    G3: x · x−1 ≈ x−1 · x ≈ 1

    Prove that we can weaken the axioms for a group (G; ∗) as
    follows.
    1. The binary operation is associative.
    2. There exists a left identity e in G such that ex = x for all x 2 G.
    3. For each a 2 G there exists a left inverse a0 2 G such that a0a = e
    -}

    e : X
    _·_ : X → X → X
    i : X → X
    ass : ∀ a b c → ((a · b) · c) == (a · (b · c))
    unit-l : ∀ a → (e · a) == a
    inv-l : ∀ a → ((i a) · a) == e
    set : is-hset X

  abstract

    {- A left inverse is also a right inverse -}
    inv-r : ∀ a → (a · (i a)) == e
    inv-r a =
      begin
      a · (i a)
      ==⟨ ! (unit-l (a · (i a))) ⟩
      e · (a · (i a))
      ==⟨ ! (ass e a (i a) ) ⟩
      (e · a) · (i a)
      ==⟨ transport (λ y → ((e · a) · (i a)) == ((y · a) · (i a))) (! (inv-l (i a))) idp ⟩
      (((i (i a)) · (i a) ) · a) · (i a)
      ==⟨ transport (λ y → ( (((i (i a)) · (i a) ) · a) · (i a) ) == (y · (i a))) (ass (i (i a)) (i a) a) idp ⟩
      ((i (i a)) · ((i a)  · a)) · (i a)
      ==⟨ transport (λ y →  (((i (i a)) · ((i a)  · a)) · (i a)) == (((i (i a)) · y) · (i a))) (inv-l a) idp ⟩
      ((i (i a)) · e) · (i a)
      ==⟨  ass (i (i a)) e (i a) ⟩
      (i (i a)) · ( e · (i a))
      ==⟨ transport (λ y → ((i (i a)) · (e · (i a))) == ((i (i a)) · y ) ) (unit-l (i a)) idp ⟩
      (i (i a)) · (i a)
      ==⟨ inv-l (i a) ⟩
      e
      ∎

    {- A left unit is also a right unit -}
    unit-r : ∀ a → (a · e) == a
    unit-r a =
      begin
      a · e
      ==⟨ transport (λ y → (a · e) == (a · y)) (! (inv-l a)) idp ⟩
      a · ( (i a) · a)
      ==⟨ ! (ass a (i a) a) ⟩
      (a · (i a)) · a
      ==⟨ transport (λ y → ((a · (i a)) · a) == (y · a)) (inv-r a) idp ⟩
      e · a
      ==⟨ unit-l a ⟩
      a
      ∎

    {- Solving an equation -}
    solv : ∀ a b x → (x == ((i a) · b)) → ((a · x) == b)
    solv a b x eq =
      begin
      (a · x)
      ==⟨ substitute (λ y → a · y) eq ⟩
      (a · ((i a) · b))
      ==⟨ ! (ass a (i a) b) ⟩
      ((a · (i a)) · b)
      ==⟨ substitute (λ y → y · b) (inv-r a) ⟩
      e · b
      ==⟨ unit-l b ⟩
      b
      ∎

    {- Solving an equation part 2 -}
    unique-solv : ∀ a b x → ((a · x) == b) → (x == ((i a) · b))
    unique-solv a b x eq =
      begin
      x
      ==⟨ ! (unit-l x) ⟩
      e · x
      ==⟨ substitute (λ y → y · x) (! (inv-l a)) ⟩
      ((i a) · a) · x
      ==⟨ ass (i a) a x ⟩
      (i a) · (a · x)
      ==⟨ substitute (λ y → (i a) · y) eq ⟩
      (i a) · b
      ∎

    {- Group computation is a congruence -}
    comp-is-congr : ∀ a b x y → (a == b) → (x == y) → ((a · x) == (b · y))
    comp-is-congr a .a x .x idp idp = idp 


record Group ℓ : Set (lsucc ℓ) where
  constructor group
  field
    U : Set ℓ
    struct : is-group U
  open is-group struct renaming (_·_ to comp) public

idf : ∀ {i} {X : Set i} → (X → X)
idf X = X

record Subgrp {i j} (G : Group i) : Set (lmax (lsucc j) i) where
  private
    module G = Group G
  field
    prop : G.U → Set j
    f : ∀ {a : G.U} → is-hprop( prop a)
    id : prop G.e
    comp : ∀ {a b : G.U} → prop a → prop b → prop (G.comp a b)

  abstract 
    prop-equality : ∀ a b → (a == b) → prop a → prop b
    prop-equality a .a idp aprop = aprop

{- Normal subgroups : -}
is-normal : {ℓ : ULevel} {Grp : Group ℓ} → (Subgrp {ℓ} {ℓ} Grp) → Set ℓ
is-normal {ℓ} {Grp} H = (g : U) → (h : U) → prop h → prop (g ×ᴳ (h ×ᴳ (iᴳ g)))
  where
    open Group Grp renaming (comp to _×ᴳ_; i to iᴳ)
    open Subgrp H renaming (comp to _×ᴴ_)

record GroupHom {i j} (G : Group i) (H : Group j) : Set (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
    _·ᴳ_ = G.comp
    _·ᴴ_ = H.comp

  field
    f : G.U → H.U
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)

  private
    prod-with-inv : (x y : G.U) → f (x ·ᴳ (G.i y)) == ((f x) ·ᴴ H.i (f y))
    prod-with-inv x y =
      begin
        f (x ·ᴳ (G.i y))
      ==⟨ ! (H.unit-r (f (x ·ᴳ (G.i y)))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ H.e
      ==⟨ ap (λ φ → ((f (x ·ᴳ (G.i y)))) ·ᴴ φ) (! (H.inv-r (f y))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ ((f y) ·ᴴ (H.i (f y)))
      ==⟨ ! (H.ass (f (x ·ᴳ (G.i y))) (f y) (H.i (f y))) ⟩
        ((f (x ·ᴳ (G.i y))) ·ᴴ (f y)) ·ᴴ (H.i (f y))
      ==⟨ ap (λ φ → φ ·ᴴ H.i (f y)) lemma ⟩
        (f x) ·ᴴ (H.i (f y))
      ∎
      where
        lemma : ((f (x ·ᴳ (G.i y))) ·ᴴ (f y)) == (f x)
        lemma =
          begin
            ((f (x ·ᴳ (G.i y))) ·ᴴ (f y))
          ==⟨ ! (pres-comp (x ·ᴳ (G.i y)) y) ⟩
            f ((x ·ᴳ (G.i y)) ·ᴳ y)
          ==⟨ ap f (G.ass x (G.i y) y) ⟩
            f (x ·ᴳ ((G.i y) ·ᴳ y))
          ==⟨ ap (λ φ → f (x ·ᴳ φ)) (G.inv-l y) ⟩
            f (x ·ᴳ G.e)
          ==⟨ ap f (G.unit-r x) ⟩
            f x
          ∎

  abstract
    {- We prove the following lemma: every homomorphism maps the identity to the identity -}
    id-to-id : (f G.e == H.e)
    id-to-id =
        begin
          f G.e
        ==⟨ ap f (! (G.inv-r G.e)) ⟩
          f (G.e ·ᴳ (G.i G.e))
        ==⟨ prod-with-inv G.e G.e ⟩
          (f G.e) ·ᴴ (H.i (f G.e))
        ==⟨ H.inv-r (f G.e) ⟩
          H.e
        ∎

    {- Preserves inverse -}
    pres-i : ∀ g → f (G.i g) == H.i (f g)
    pres-i g =
      begin
        f (G.i g)
      ==⟨ ap f (! (G.unit-l (G.i g))) ⟩
        f (G.e ·ᴳ (G.i g))
      ==⟨ prod-with-inv G.e g ⟩
        (f G.e) ·ᴴ (H.i (f g))
      ==⟨ ap (λ φ → φ ·ᴴ (H.i (f g))) id-to-id ⟩
        H.e ·ᴴ H.i (f g)
      ==⟨ H.unit-l (H.i (f g)) ⟩
        H.i (f g)
      ∎

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

→ᴳ-id : ∀ {i} {G : Group i} → G →ᴳ G
→ᴳ-id = group-hom (λ x → x) (λ g₁ g₂ → idp)

→ᴳ-trans : ∀ {i j k} {G : Group i} {H : Group j} {J : Group k} → G →ᴳ H → H →ᴳ J → G →ᴳ J
→ᴳ-trans (group-hom g p) (group-hom h q) =
  group-hom (λ z → h (g z)) (λ a b → transitive (ap h (p a b)) (q (g a) (g b)))

_≃ᴳ_ : ∀ {i j} (G : Group i) (H : Group j) → Set (lmax i j)
G ≃ᴳ H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))
infix 100 _≃ᴳ_
module _≃ᴳ_ {i j} {G : Group i} {H : Group j} (iso : G ≃ᴳ H) where

  open Group H renaming (comp to _×ᴴ_)
  open Group G renaming (comp to _×ᴳ_)
  open GroupHom (Σ.fst iso)
  open is-hae (is-equiv→is-hae f (Σ.snd iso))

  preserves-comp : (a' b' : Group.U H) → g (Group.comp H a' b') == Group.comp G (g a') (g b')
  preserves-comp a' b' =
    begin
      g (a' ×ᴴ b')
    ==⟨ ap g (ap2 (! (f-g a')) (! (f-g b')) {_×ᴴ_}) ⟩
      g ((f (g a')) ×ᴴ (f (g b')))
    ==⟨ ap g (! (pres-comp (g a') (g b'))) ⟩
      g (f ((g a') ×ᴳ (g b')))
    ==⟨ g-f (((g a') ×ᴳ (g b'))) ⟩
      (g a') ×ᴳ (g b')
    ∎

  g-hom : H →ᴳ G
  g-hom = group-hom g preserves-comp

  f-hom : G →ᴳ H
  f-hom = Σ.fst iso

  adj' : (a' : Group.U H) → ap g (f-g a') == g-f (g a')
  adj' a' = is-group.set
    (Group.struct G)
    (g (f (g a')))
    (g a')
    (ap g (f-g a'))
    (g-f (g a'))

  sym : (H ≃ᴳ G)
  sym = g-hom , is-hae→is-equiv g (record { g = f
                                          ; f-g = g-f
                                          ; g-f = f-g
                                          ; adj = adj' })

–>ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (iso : G ≃ᴳ H) → (G →ᴳ H)
–>ᴳ = _≃ᴳ_.f-hom

<–ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (G ≃ᴳ H) → (H →ᴳ G)
<–ᴳ = _≃ᴳ_.g-hom

sym : ∀ {i j} (G : Group i) (H : Group j) → (G ≃ᴳ H) → (H ≃ᴳ G)
sym G H = _≃ᴳ_.sym
