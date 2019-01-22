{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences2
open import Eq-reasoning


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