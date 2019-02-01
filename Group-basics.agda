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

{- We can weaken the axioms for a group (G; ∗) as
   follows.
   1. The binary operation is associative.
   2. There exists a left identity e in G such that ex = x for all x 2 G.
   3. For each a 2 G there exists a left inverse a0 2 G such that a0a = e
-}
module _ {α : ULevel} where

  {- In this module we define the properties that a group ought to have -}
  module Properties where

    {- Definition of the properties that a group has. We take the axioms as weak as possible. -}
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

    {- We define when a Magma is a group. We use sigma types instead of a record type for more compatibility with the library  -}
    is-group : Magma → Type α
    is-group M =  is-associative (Magma._∗_ M) × is-set (Magma.X M)
               × (Σ (has-unit-l (Magma._∗_ M))
                    λ { (e , isUnit) → has-inverse-l (Magma._∗_ M) e})

  {- We define a group as a Magma with the additional structure above -}
  record Group : Set (lsucc α) where
    constructor group
    field
      M : Magma
      is-group : Properties.is-group M

    {- For convenience we extract all the useful fields of a group, so that we don't have to extract them every time from the sigma types -}
    U : Type α
    U = Magma.X M

    e : U
    e = (fst ∘ fst ∘ snd ∘ snd) is-group

    comp : U → U → U
    comp = Magma._∗_ M

    _·_ = comp

    i : U → U
    i = (fst ∘ snd ∘ snd ∘ snd) is-group

    associative : (a b c : U) → ((a · b) · c) == (a · (b · c))
    associative = (fst is-group)

    inv-l : (a : U) → ((i a) · a) == e
    inv-l = (snd ∘ snd ∘ snd ∘ snd) is-group

    unit-l : (a : U) → (e · a) == a
    unit-l = (snd ∘ fst ∘ snd ∘ snd) is-group

    set : is-set U
    set = (fst ∘ snd) is-group

    {- We use equational reasoning to prove basic group-theoretical lemma's based on the axioms -}
    {- A left inverse is also a right inverse -}
    inv-r : (a : U) → (a · (i a)) == e
    inv-r a =
        a · (i a)
      =⟨ ! (unit-l (a · (i a))) ⟩
        e · (a · (i a))
      =⟨ ! (associative e a (i a)) ⟩
        (e · a) · (i a)
      =⟨ ap (λ φ → (φ · a) · i a) (! (inv-l (i a))) ⟩
        (((i (i a)) · (i a)) · a) · (i a)
      =⟨ ap (λ φ → φ · (i a)) (associative (i (i a)) (i a) a) ⟩
        ((i (i a)) · ((i a)  · a)) · (i a)
      =⟨ ap (λ φ → ((i (i a)) · φ) · (i a)) (inv-l a) ⟩
        ((i (i a)) · e) · (i a)
      =⟨ associative (i (i a)) e (i a) ⟩
        (i (i a)) · (e · (i a))
      =⟨ ap (λ φ → (i (i a)) · φ) (unit-l (i a)) ⟩
        (i (i a)) · (i a)
      =⟨ inv-l (i a) ⟩
        e
      =∎

    {- A left unit is also a right unit -}
    unit-r : (a : U) → (a · e) == a
    unit-r a =
        a · e
      =⟨ ap (λ φ → (a · φ)) (! (inv-l a)) ⟩
        a · ( (i a) · a)
      =⟨ ! (associative a (i a) a) ⟩
        (a · (i a)) · a
      =⟨ ap (λ φ → (φ · a)) (inv-r a) ⟩
        e · a
      =⟨ unit-l a ⟩
        a
      =∎

    {- Solving an equation part 1 -}
    solv : (a b x : U) → (x == ((i a) · b)) → ((a · x) == b)
    solv a b x eq =
      (a · x)
      =⟨ ap (λ y → a · y) eq ⟩
      (a · ((i a) · b))
      =⟨ ! (associative a (i a) b) ⟩
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
      =⟨ associative (i a) a x ⟩
      (i a) · (a · x)
      =⟨ ap (λ y → (i a) · y) eq ⟩
      (i a) · b
      =∎

    {- Solving an equation part 3 : solutions to an equation are unique -}
    unique-solve : ∀ a b x y → (a · x) == b → (a · y) == b → x == y
    unique-solve a b x y p q =
      x =⟨ unique-solv a b x p ⟩
      (i a) · b =⟨ ! (unique-solv a b y q) ⟩
      y =∎

    {- Group computation is a congruence -}
    comp-is-congr : ∀ a b x y → (a == b) → (x == y) → ((a · x) == (b · y))
    comp-is-congr a .a x .x idp idp = idp

    {- the inverse of the inverse is the element itself -}
    inv-inv-is-unit : ∀ a → (i (i a)) == a
    inv-inv-is-unit a = 
      i (i a) =⟨ ! (unit-l (i (i a))) ⟩
      e · (i (i a)) =⟨ ap (λ x → x · (i (i a))) (! (inv-r a)) ⟩
      (a · (i a)) · (i (i a)) =⟨ associative a (i a) (i (i a)) ⟩
      a · ( (i a) · (i (i a)) ) =⟨ ap (λ x → a · x) (inv-r (i a)) ⟩
      a · e =⟨ unit-r a ⟩
      a =∎

    {- Inverses are unique -}
    inv-is-unique : ∀ a i' → ((a · i') == e) → (i' == (i a))
    inv-is-unique a i' p = unique-solve a e i' (i a) p (inv-r a)

    {- the inverse of (a · b) is equal to (i b) · (i a) -}
    inv-of-comp : ∀ a b → ((i b) · (i a)) == (i (a · b))
    inv-of-comp a b = inv-is-unique (a · b) ((i b) · (i a)) path
      where
        path : ((a · b) · (i b · i a)) == e
        path = 
          (a · b) · (i b · i a) =⟨ ! (associative (a · b) (i b) (i a)) ⟩
          ((a · b) · i b) · (i a) =⟨ ap (λ φ → φ · (i a)) (associative a b (i b)) ⟩
          (a · (b · i b)) · (i a) =⟨ ap (λ φ → (a · φ) · (i a)) (inv-r b) ⟩
          (a · e) · (i a) =⟨ ap (λ φ → φ · (i a)) (unit-r a) ⟩
          a · (i a) =⟨ inv-r a ⟩
          e =∎

  {- We define the type subgroup, it is a dependent type, depending on the group G -}
  record Subgrp (G : Group) : Set (lsucc α) where
    private
      module G = Group G
    field
      prop : G.U → Set α --the function selects the elements in the subgroup, as general as possible 
      f : ∀ {a : G.U} → is-prop( prop a) -- the selection function has to map to a proposition
      id : prop G.e -- unit has to be in the subgroup
      comp : ∀ {a b : G.U} → prop a → prop b → prop (G.comp a b) --subgroup closed under group product
      inv : ∀ {a : G.U} → prop a → prop (G.i a) --subgroup closed under inverses

    {- If two subgroups are equal, then their props are equivalent -}
    prop-equality : ∀ a b → (a == b) → prop a → prop b
    prop-equality a .a idp aprop = aprop

  {- Definition of normal subgroups. A dependent type, depending on a group G (implicit) and a subgroup H of type Subgrp G -}
  {- We use the most common definition : ∀ g ∈ G, ∀ h ∈ H : g · h · (i g) ∈ H -}
  is-normal : {G : Group} → (Subgrp G) → Set α
  is-normal {G} H = (g : U) → (h : U) → prop h → prop (g ·ᴳ (h ·ᴳ (iᴳ g)))
    where
      open Group G renaming (comp to _·ᴳ_; i to iᴳ)
      open Subgrp H renaming (comp to _·ᴴ_)

{- Definition of the type group homomorphism G →ᴳ H, a dependent type, depending on two groups G and H -}
record GroupHom {α β : ULevel} (G : Group {α}) (H : Group {β}) : Set (lmax α β) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
    _·ᴳ_ = G.comp
    _·ᴴ_ = H.comp

  field
    f : G.U → H.U --underlying map of the homomorphism
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂) --condition that it preserves the group structure 

  private
    {- a homomorphism respects group product and inverses -}
    prod-with-inv : (x y : G.U) → f (x ·ᴳ (G.i y)) == ((f x) ·ᴴ H.i (f y))
    prod-with-inv x y =
        f (x ·ᴳ (G.i y))
      =⟨ ! (H.unit-r (f (x ·ᴳ (G.i y)))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ H.e
      =⟨ ap (λ φ → ((f (x ·ᴳ (G.i y)))) ·ᴴ φ) (! (H.inv-r (f y))) ⟩
        (f (x ·ᴳ (G.i y))) ·ᴴ ((f y) ·ᴴ (H.i (f y)))
      =⟨ ! (H.associative (f (x ·ᴳ (G.i y))) (f y) (H.i (f y))) ⟩
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
          =⟨ ap f (G.associative x (G.i y) y) ⟩
            f (x ·ᴳ ((G.i y) ·ᴳ y))
          =⟨ ap (λ φ → f (x ·ᴳ φ)) (G.inv-l y) ⟩
            f (x ·ᴳ G.e)
          =⟨ ap f (G.unit-r x) ⟩
            f x
          =∎

  abstract
    {- A homomorphism maps the identity to the identity -}
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

    {- A homomorphism preserves inverses -}
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

{- we introduce some useful infix notation for homomorphisms -}
infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

{- gives the trivial automorphism for a group G -}
→ᴳ-id : {α : ULevel} {G : Group {α}} → G →ᴳ G
→ᴳ-id = group-hom (λ x → x) (λ g₁ g₂ → idp)

{- composition of two homomorphisms is again a homomorphism -}
→ᴳ-trans : {α β γ : ULevel} {G : Group {α}} {H : Group {β}} {J : Group {γ}} → (G →ᴳ H) → (H →ᴳ J) → (G →ᴳ J)
→ᴳ-trans (group-hom g p) (group-hom h q) =
  group-hom (λ z → h (g z)) (λ a b → (ap h (p a b)) ∙ (q (g a) (g b)))

{- definition of isomorphism G ≃ᴳ H: a homomorphism G →ᴳ H + a proof that the underlying map is an equivalence, so we have a bijection -}
_≃ᴳ_ : {α β : ULevel} (G : Group {α}) (H : Group {β}) → Set (lmax α β)
G ≃ᴳ H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))
infix 100 _≃ᴳ_

{- In this module we define and prove some things for isomorphism -}
module _≃ᴳ_ {α β : ULevel} {G : Group {α}} {H : Group {β}} (iso : G ≃ᴳ H) where
  open Group H renaming (comp to _·ᴴ_)
  open Group G renaming (comp to _·ᴳ_)
  open GroupHom (Σ.fst iso)
  open is-equiv (Σ.snd iso)

  private
    {- Auxiliary lemma : Action path over binary function. -}
    ap2 : ∀ {i j k} {X : Set i} {Y : Set j} {Z : Set k} {x x' : X} {y y' : Y}
        (p : x == x') (q : y == y') {rel : X → Y → Z}
        → rel x y == rel x' y'
    ap2 idp idp = idp

  {- The inverse map of the isomorphism also preserves computation -}
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

  {- Extract homomorphisms going both ways from the isomorphism -}
  g-hom : H →ᴳ G
  g-hom = group-hom g preserves-comp

  f-hom : G →ᴳ H
  f-hom = Σ.fst iso

  {- Isomorphism is reflexive -}
  sym : (H ≃ᴳ G)
  sym = g-hom , is-eq g f g-f f-g

sym : {α β : ULevel} (G : Group {α}) (H : Group {β}) → (G ≃ᴳ H) → (H ≃ᴳ G)
sym G H = _≃ᴳ_.sym
