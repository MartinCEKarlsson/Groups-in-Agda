{-# OPTIONS --without-K --rewriting #-}
open import Magma-basics

open import lib.Equivalence
open import lib.Base
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Sigma

{- This file draws heavily from the HOTT-library -}
{- In this file we have the basic definitions of groups, subgroups, normal subgroups, and group homomorphisms + basic lemma's -}
{- PLEASE ONLY PUSH THIS FILE IF IT LOADS WITHOUT OPEN GOALS, OTHERWISE THE OTHER FILES WILL NOT LOAD -}

module Group-basics where
{- A group G is an algebra hG; ·; −1; 1i with a binary, a unary, and
   nullary operation in which the following identities are true:
   G1: x · (y · z) ≈ (x · y) · z
   G2: x · 1 ≈ 1 · x ≈ x
   G3: x · x−1 ≈ x−1 · x ≈ 1
-}

{- Prove that we can weaken the axioms for a group (G; ∗) as
   follows.
   1. The binary operation is associative.
   2. There exists a left identity e in G such that ex = x for all x 2 G.
   3. For each a 2 G there exists a left inverse a0 2 G such that a0a = e
-}
module _ {α : ULevel} where

  {- Definition of the properties that a group has. -}
  is-associative : {X : Type α} (_⋆_ : X → X → X) → Type α
  is-associative {X} _⋆_ = ((a b c : X) → ((a ⋆ b) ⋆ c) == (a ⋆ (b ⋆ c)))

  is-unit-l : {X : Type α} (_⋆_ : X → X → X) → X → Type α
  is-unit-l {X} _⋆_ e = ((a : X) → (e ⋆ a) == a)

  is-inverse-l : {X : Type α} (_⋆_ : X → X → X) (e : X) (i : X → X) → Type α
  is-inverse-l {X} _⋆_ e i = ((a : X) → ((i a) ⋆ a) == e)

  has-unit-l : {X : Type α} (_⋆_ : X → X → X) → Type α
  has-unit-l {X} _⋆_ = Σ X (is-unit-l _⋆_)

  has-inverse-l : {X : Type α} (_⋆_ : X → X → X) (e : X) → Type α
  has-inverse-l {X} _⋆_ e = Σ (X → X) (is-inverse-l _⋆_ e)

  is-group : Magma → Type α
  is-group M =  is-associative (Magma._∗_ M) × is-set (Magma.X M)
             × (Σ (has-unit-l (Magma._∗_ M))
                  λ { (e , isUnit) → has-inverse-l (Magma._∗_ M) e})

  record Group : Set (lsucc α) where
    constructor group
    field
      M : Magma
      is-groupl : is-group M


    U : Type α
    U = Magma.X M

    e : U
    e = (fst ∘ fst ∘ snd ∘ snd) is-groupl

    comp : U → U → U
    comp = Magma._∗_ M

    _·_ = comp

    i : U → U
    i = (fst ∘ snd ∘ snd ∘ snd) is-groupl

    ass : (a b c : U) → ((a · b) · c) == (a · (b · c))
    ass = (fst is-groupl)

    inv-l : (a : U) → ((i a) · a) == e
    inv-l = (snd ∘ snd ∘ snd ∘ snd) is-groupl

    unit-l : (a : U) → (e · a) == a
    unit-l = (snd ∘ fst ∘ snd ∘ snd) is-groupl

    set : is-set U
    set = (fst ∘ snd) is-groupl

    inv-r : (a : U) → (a · (i a)) == e
    inv-r a =
        a · (i a)
      =⟨ ! (unit-l (a · (i a))) ⟩
        e · (a · (i a))
      =⟨ ! (ass e a (i a)) ⟩
        (e · a) · (i a)
      =⟨ ap (λ φ → (φ · a) · i a) (! (inv-l (i a))) ⟩
        (((i (i a)) · (i a)) · a) · (i a)
      =⟨ ap (λ φ → φ · (i a)) (ass (i (i a)) (i a) a) ⟩
        ((i (i a)) · ((i a)  · a)) · (i a)
      =⟨ ap (λ φ → ((i (i a)) · φ) · (i a)) (inv-l a) ⟩
        ((i (i a)) · e) · (i a)
      =⟨ ass (i (i a)) e (i a) ⟩
        (i (i a)) · (e · (i a))
      =⟨ ap (λ φ → (i (i a)) · φ) (unit-l (i a)) ⟩
        (i (i a)) · (i a)
      =⟨ inv-l (i a) ⟩
        e
      =∎

    unit-r : (a : U) → (a · e) == a
    unit-r a =
        a · e
      =⟨ ap (λ φ → (a · φ)) (! (inv-l a)) ⟩
        a · ( (i a) · a)
      =⟨ ! (ass a (i a) a) ⟩
        (a · (i a)) · a
      =⟨ ap (λ φ → (φ · a)) (inv-r a) ⟩
        e · a
      =⟨ unit-l a ⟩
        a
      =∎

      {- Solving an equation -}
    solv : (a b x : U) → (x == ((i a) · b)) → ((a · x) == b)
    solv a b x eq =
      (a · x)
      =⟨ ap (λ y → a · y) eq ⟩
      (a · ((i a) · b))
      =⟨ ! (ass a (i a) b) ⟩
      ((a · (i a)) · b)
      =⟨ ap (λ y → y · b) (inv-r a) ⟩
      e · b
      =⟨ unit-l b ⟩
      b
      =∎

    {- Solving an equation part 2 -}
    unique-solv : ∀ a b x → ((a · x) == b) → (x == ((i a) · b))
    unique-solv a b x eq =
      x
      =⟨ ! (unit-l x) ⟩
      e · x
      =⟨ ap (λ y → y · x) (! (inv-l a)) ⟩
      ((i a) · a) · x
      =⟨ ass (i a) a x ⟩
      (i a) · (a · x)
      =⟨ ap (λ y → (i a) · y) eq ⟩
      (i a) · b
      =∎

    {- Group computation is a congruence -}
    comp-is-congr : ∀ a b x y → (a == b) → (x == y) → ((a · x) == (b · y))
    comp-is-congr a .a x .x idp idp = idp

  module _ {β : ULevel} where
    record Subgrp (G : Group) : Set (lmax α (lsucc β)) where
      private
        module G = Group G
      field
        prop : G.U → Set β
        f : ∀ {a : G.U} → is-prop( prop a)
        id : prop G.e
        comp : ∀ {a b : G.U} → prop a → prop b → prop (G.comp a b)
        inv : ∀ {a : G.U} → prop a → prop (G.i a)

      prop-equality : ∀ a b → (a == b) → prop a → prop b
      prop-equality a .a idp aprop = aprop

    {- Normal subgroups : -}
    is-normal : {Grp : Group} → (Subgrp Grp) → Set (lmax α β)
    is-normal {Grp} H = (g : U) → (h : U) → prop h → prop (g ·ᴳ (h ·ᴳ (iᴳ g)))
      where
        open Group Grp renaming (comp to _·ᴳ_; i to iᴳ)
        open Subgrp H renaming (comp to _·ᴴ_)

record GroupHom {α β : ULevel} (G : Group {α}) (H : Group {β}) : Set (lmax α β) where
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
        f (x ·ᴳ (G.i y))
      =⟨ ! (H.unit-r (f (x ·ᴳ (G.i y)))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ H.e
      =⟨ ap (λ φ → ((f (x ·ᴳ (G.i y)))) ·ᴴ φ) (! (H.inv-r (f y))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ ((f y) ·ᴴ (H.i (f y)))
      =⟨ ! (H.ass (f (x ·ᴳ (G.i y))) (f y) (H.i (f y))) ⟩
        ((f (x ·ᴳ (G.i y))) ·ᴴ (f y)) ·ᴴ (H.i (f y))
      =⟨ ap (λ φ → φ ·ᴴ H.i (f y)) lemma ⟩
        (f x) ·ᴴ (H.i (f y))
      =∎
      where
        lemma : ((f (x ·ᴳ (G.i y))) ·ᴴ (f y)) == (f x)
        lemma =
            ((f (x ·ᴳ (G.i y))) ·ᴴ (f y))
          =⟨ ! (pres-comp (x ·ᴳ (G.i y)) y) ⟩
            f ((x ·ᴳ (G.i y)) ·ᴳ y)
          =⟨ ap f (G.ass x (G.i y) y) ⟩
            f (x ·ᴳ ((G.i y) ·ᴳ y))
          =⟨ ap (λ φ → f (x ·ᴳ φ)) (G.inv-l y) ⟩
            f (x ·ᴳ G.e)
          =⟨ ap f (G.unit-r x) ⟩
            f x
          =∎

  abstract
    {- Lemma: every homomorphism maps the identity to the identity -}
    id-to-id : (f G.e == H.e)
    id-to-id =
          f G.e
        =⟨ ap f (! (G.inv-r G.e)) ⟩
          f (G.e ·ᴳ (G.i G.e))
        =⟨ prod-with-inv G.e G.e ⟩
          (f G.e) ·ᴴ (H.i (f G.e))
        =⟨ H.inv-r (f G.e) ⟩
          H.e
        =∎

    {- Preserves inverse -}
    pres-i : ∀ g → f (G.i g) == H.i (f g)
    pres-i g =
        f (G.i g)
      =⟨ ap f (! (G.unit-l (G.i g))) ⟩
        f (G.e ·ᴳ (G.i g))
      =⟨ prod-with-inv G.e g ⟩
        (f G.e) ·ᴴ (H.i (f g))
      =⟨ ap (λ φ → φ ·ᴴ (H.i (f g))) id-to-id ⟩
        H.e ·ᴴ H.i (f g)
      =⟨ H.unit-l (H.i (f g)) ⟩
        H.i (f g)
      =∎

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

→ᴳ-id : {α : ULevel} {G : Group {α}} → G →ᴳ G
→ᴳ-id = group-hom (λ x → x) (λ g₁ g₂ → idp)

→ᴳ-trans : {α β γ : ULevel}{G : Group {α}} {H : Group {β}} {J : Group {γ}} → (G →ᴳ H) → (H →ᴳ J) → (G →ᴳ J)
→ᴳ-trans (group-hom g p) (group-hom h q) =
  group-hom (λ z → h (g z)) (λ a b → (ap h (p a b)) ∙ (q (g a) (g b)))

_≃ᴳ_ : {α β : ULevel} (G : Group {α}) (H : Group {β}) → Set (lmax α β)
G ≃ᴳ H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))
infix 100 _≃ᴳ_
module _≃ᴳ_ {α β : ULevel} {G : Group {α}} {H : Group {β}} (iso : G ≃ᴳ H) where
  open Group H renaming (comp to _·ᴴ_)
  open Group G renaming (comp to _·ᴳ_)
  open GroupHom (Σ.fst iso)
  open is-equiv (Σ.snd iso)

  private
    {- Action path over binary function. -}
    ap2 : ∀ {i j k} {X : Set i} {Y : Set j} {Z : Set k} {x x' : X} {y y' : Y}
        (p : x == x') (q : y == y') {rel : X → Y → Z}
        → rel x y == rel x' y'
    ap2 idp idp = idp

  preserves-comp : (a' b' : Group.U H) → g (a' ·ᴴ b') == (g a' ·ᴳ g b')
  preserves-comp a' b' =
      g (a' ·ᴴ b')
    =⟨ ap g (ap2 (! (f-g a')) (! (f-g b')) {_·ᴴ_}) ⟩
      g ((f (g a')) ·ᴴ (f (g b')))
    =⟨ ap g (! (pres-comp (g a') (g b'))) ⟩
      g (f ((g a') ·ᴳ (g b')))
    =⟨ g-f (((g a') ·ᴳ (g b'))) ⟩
      (g a') ·ᴳ (g b')
    =∎

  g-hom : H →ᴳ G
  g-hom = group-hom g preserves-comp

  f-hom : G →ᴳ H
  f-hom = Σ.fst iso

  sym : (H ≃ᴳ G)
  sym = g-hom , is-eq g f g-f f-g

–>ᴳ : {α β : ULevel} {G : Group {α}} {H : Group {β}} → (iso : G ≃ᴳ H) → (G →ᴳ H)
–>ᴳ = _≃ᴳ_.f-hom

<–ᴳ : {α β : ULevel} {G : Group {α}} {H : Group {β}} → (G ≃ᴳ H) → (H →ᴳ G)
<–ᴳ = _≃ᴳ_.g-hom

sym : {α β : ULevel} (G : Group {α}) (H : Group {β}) → (G ≃ᴳ H) → (H ≃ᴳ G)
sym G H = _≃ᴳ_.sym
