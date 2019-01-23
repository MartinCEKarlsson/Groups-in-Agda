{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences2
open import Eq-reasoning
--open import lib.Basics

-- test
{- This file draws heavily from the HOTT-library -}

{- A type is an h-proposition or mere proposition if we can (uniformly) construct a path
   between any two points.
-}
is-hprop : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hprop X = (x y : X) → (x == y)

{- A type is an h-set if every identity type is an h-proposition. -}
is-hset : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hset X = (x y : X) → is-hprop (x == y)




record is-group {ℓ} (X : Set ℓ) (e : X) (_·_ : X → X → X) (i : X → X) : Set ℓ where
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
    ass : ∀ a b c → ((a · b) · c) == (a · (b · c))
    is-unit : ∀ a → (a · e) == e
    inv₁ : ∀ a → ((i a) · a) == e
    inv₂ : ∀ a → (a · (i a)) == e
    proof : is-hset X

  asdf : ∀ a → (a · e) == e → e == (a · e)
  asdf = λ a x → symmetric (a · e) e x

  e==e : e == e
  e==e =
    begin
      e
    ==⟨ idp ⟩
      e
    ∎


  asdf2 : (e · e) == e → e == (e · e)
  asdf2 = symmetric (e · e) e

  asdf3 : e == (e · e)
  asdf3 = asdf2 (is-unit e)
  abstract
    e==e·e : e == (e · e)
    e==e·e =
      begin
        e
      ==⟨ asdf2 (is-unit e) ⟩
        e · e
      ∎

open is-group

record Group ℓ : Set (lsucc ℓ) where
  constructor group
  field
    U : Set ℓ
    e : U
    comp : U → U → U
    i : U → U
    proof : is-group U e comp i

idf :  (X : Set ) → X → X
idf X x = x

record Subgrp {i j} (G : Group i) : Set (lmax (lsucc j) i) where
  private
    module G = Group G
  field
    prop : G.U → Set j
    f : ∀ {a : G.U} → is-hprop( prop a)
    id : prop G.e
    comp : ∀ {a b : G.U} → prop a → prop b → prop (G.comp a b)

{- Normal subgroups : -}
is-normal : {ℓ : ULevel} {Grp : Group ℓ} → (Subgrp {ℓ} {ℓ} Grp) → Set ℓ
is-normal {ℓ} {Grp} H = (g : U) → (h : U) → prop h → prop (g ×ᴳ (h ×ᴳ (i g)))
  where 
    open Group Grp renaming (comp to _×ᴳ_)
    open Subgrp H renaming (comp to _×ᴴ_)

record GroupHom {i j} (G : Group i) (H : Group j) : Set (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
  field
    f : G.U → H.U
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)

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
  adj' a' = proof
    (Group.proof G)
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
sym G H x = _≃ᴳ_.sym x

==a : ∀ {i} {G : Group i} {H : Group i} → (G ≃ᴳ H) → (H == G)
==a = {!   !}

{- We prove the following lemma: every homomorphism maps the identity to the identity -}
id-to-id : {i : ULevel} {G H : Group i} → (f : G →ᴳ H) → (GroupHom.f f (Group.e G) == Group.e H)
id-to-id = {!!}

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : ∀ {i} {G H : Group i} → (G == H) → (G ≃ᴳ H)
idtoiso {i} {G} {.G} idp = →ᴳ-id , (λ y → build-is-contr (y , idp) (λ {(x , idp) → idp}))

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
idtoiso-subgrp {i} {G} {H} p G' = record { prop = λ x → Subgrp.prop G' (θ-inv(x)) ; f = Subgrp.f G' ; id = {!!}  ; comp = {!!} }
  where
    open Group H renaming (comp to _×ᴴ_)
    open Group G renaming (comp to _×ᴳ_)

    equiv : (G ≃ᴳ H) -- The equivalence
    equiv = idtoiso p

    open GroupHom (Σ.fst equiv)

    θ : (Group.U G → Group.U H)   -- The forward map of the equivalence
    θ = GroupHom.f (Σ.fst equiv)

    open is-hae (is-equiv→is-hae θ (Σ.snd equiv))

    θ-inv : (Group.U H → Group.U G)  -- The backward map of the equivalence
    θ-inv = g

{- We want to prove that the previous two functions Subgrp G → Subgrp H are homotopic -}
trans-equiv-idtoiso : {i : ULevel} (G H : Group i) → transp-subgrp {i} {G} {H} == idtoiso-subgrp {i} {G} {H}
trans-equiv-idtoiso = {!!}


{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : {ℓ : ULevel} {G : Group ℓ} (f : (G : Group ℓ) → (Subgrp {ℓ} {ℓ} G)) → (H : Group ℓ) → (is-normal (f H))
def-subgroups-are-normal f H = {!!}






