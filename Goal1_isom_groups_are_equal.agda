{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.NType
open import lib.NType2
open import lib.Funext
open import lib.PathOver
open import lib.types.Sigma
open import lib.types.Pi
open import lib.PathGroupoid
open import lib.Univalence

open import Group-basics
open import Magma

module Goal1_isom_groups_are_equal where

{- In this file we work towards the first goal of the project: isomorphic
   groups are equal in HoTT
-}

module _ {α : ULevel} {M : Magma {α}} where
  open Magma.Magma M
  {- We want the proofs that a Magma is a group to be propositions. -}

  is-group-all-paths : (x y : is-group M) → (x == y)
  is-group-all-paths (isAssoc , isSet , (e , isUnit) , inv , isInv)
        (isAssoc' , isSet' , (e' , isUnit') , inv' , isInv')
        =   pair×= isAssoc= (pair×= isSet= (pair= unit= ↓-inv=))
    where
      module G = Group (group M (isAssoc , isSet , (e , isUnit) , inv , isInv))
      module H = Group (group M (isAssoc' , isSet' , (e' , isUnit') , inv'
                                                                    , isInv'))

      paths-are-props : {a b : X} → is-prop (a == b)
      paths-are-props {a} {b} = has-level-apply isSet a b

      isSet= : isSet == isSet'
      isSet= = prop-has-all-paths isSet isSet'

      isAssoc= : isAssoc == isAssoc'
      isAssoc= = ap (curry ∘ curry) (λ= λ {((a , b) , c) →
        prop-path paths-are-props (isAssoc a b c) (isAssoc' a b c)})

      H= : _∗_ == H.comp
      H= = idp

      e= : e == e'
      e= =
          e
        =⟨ ! (H.unit-r e) ⟩
          e ∗ e'
        =⟨ G.unit-l e' ⟩
          e'
        =∎

      isUnit= : isUnit == isUnit' [ (λ x → is-unit-l _∗_ x) ↓ e= ]
      isUnit= = from-transp ((λ x → is-unit-l _∗_ x)) e= {isUnit} (λ= (λ x →
        prop-path paths-are-props (
          (transport ((λ x → is-unit-l _∗_ x)) e= isUnit) x) (isUnit' x)))

      unit= : (e , isUnit) == (e' , isUnit')
      unit= = pair= e= isUnit=

      inv= : inv == inv'
      inv= = λ= (λ x →
          inv x
        =⟨ ! (H.unit-r (inv x)) ⟩
          (inv x) ∗ e'
        =⟨ ap (λ φ → (inv x) ∗ φ) (! (H.inv-r x)) ⟩
          (inv x) ∗ (x ∗ (inv' x))
        =⟨ ! (G.ass (inv x) x (inv' x)) ⟩
          ((inv x) ∗ x) ∗ (inv' x)
        =⟨ ap (λ φ → (φ ∗ inv' x)) (G.inv-l x) ⟩
          e ∗ inv' x
        =⟨ G.unit-l (inv' x) ⟩
          inv' x
        =∎)

      ↓-inv= : (inv , isInv) == (inv' , isInv')
                            [ (λ { (x , isU) → has-inverse-l _∗_ x}) ↓ unit= ]
      ↓-inv= = from-transp (λ x → has-inverse-l _∗_ (fst x)) unit= inv,isInv=
        where
          tpinv : (p : e , isUnit == e' , isUnit') → has-inverse-l _∗_ e'
          tpinv p = transport (λ x → has-inverse-l _∗_ (fst x)) p (inv , isInv)

          inv1= : (p : e , isUnit == e' , isUnit') → fst (tpinv p) == inv'
          inv1= idp = λ= (λ x →
              inv x
            =⟨ ap (λ f → f x) inv= ⟩
              inv' x
            =∎)

          is-inverse-l-is-prop : {inv : X → X} {e : X}
                               → is-prop (is-inverse-l _∗_ e inv)
          is-inverse-l-is-prop {inv} {e} = all-paths-is-prop (λ f g →
            λ= (λ x → prop-path paths-are-props (f x) (g x)))

          inv2= : (p : e , isUnit == e' , isUnit') → snd {α} (tpinv p) == isInv'
                                  [ (λ x → is-inverse-l _∗_ e' x) ↓ inv1= p ]
          inv2= idp = from-transp (λ x → is-inverse-l _∗_ e' x) (inv1= idp)
                                  (prop-path is-inverse-l-is-prop (transport
                                    (λ x → is-inverse-l _∗_ e' x) (inv1= idp)
                                    (snd {α} (tpinv idp)))
                                  isInv')

          inv,isInv= : {p : e , isUnit == e' , isUnit'}
                     → (tpinv p) == (inv' , isInv')
          inv,isInv= {p} = pair= (inv1= p) (inv2= p)


  is-group-is-prop : is-prop (is-group M)
  is-group-is-prop = all-paths-is-prop is-group-all-paths


  {- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
  {- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
  -- idtoiso : {α : ULevel} {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
  -- idtoiso {α} {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)
  --
  -- isotoid : {α : ULevel} {G H : Group {α}} (iso : G ≃ᴳ H) → (G == H)
  -- isotoid {α} {G} {H} iso = {!   !}
module _ {α : ULevel} where
  private

    Group' : Type (lsucc α)
    Group' = Σ Magma (λ X → (is-group X))

    Σ⟪_⟫ : Group → Group'
    Σ⟪ group M is-groupl ⟫ = M , is-groupl

    -Σ⟪_⟫ : Group' → Group
    -Σ⟪ M , is-groupl ⟫ = group M is-groupl

    Group≃Group' : Group {α} ≃ Group'
    Group≃Group' = equiv f g f-g g-f
      where
        f : Group → Group'
        f G = Σ⟪ G ⟫

        g : Group' → Group
        g G = -Σ⟪ G ⟫

        f-g : (G : Group') → (f (g G) == G)
        f-g (fst₁ , snd₁) = idp

        g-f : (G : Group) → (g (f G) == G)
        g-f M = idp

    group'= : (G H : Group') → Type α
    group'= G H = magma= (fst G) (fst H)

    iso≃group'= : (G H : Group) → (G ≃ᴳ H) ≃ (group'= Σ⟪ G ⟫ Σ⟪ H ⟫)
    iso≃group'= G H = equiv f g f-g g-f
      where

        X≃ : G ≃ᴳ H → (Magma.X (fst Σ⟪ G ⟫) ≃ Magma.X (fst Σ⟪ H ⟫))
        X≃ iso = GroupHom.f (fst iso) , snd iso

        f : G ≃ᴳ H → group'= Σ⟪ G ⟫ Σ⟪ H ⟫
        f x = record { carrier-equiv = X≃ x
                     ; preserves-operator = GroupHom.pres-comp (fst x) }

        g : group'= Σ⟪ G ⟫ Σ⟪ H ⟫ → G ≃ᴳ H
        g record { carrier-equiv = carrier-equiv
                 ; preserves-operator = preserves-operator }
               = (group-hom (–> carrier-equiv) preserves-operator) , snd carrier-equiv

        f-g : (x : group'= Σ⟪ G ⟫ Σ⟪ H ⟫) → f (g x) == x
        f-g x = idp

        g-f : (x : G ≃ᴳ H) → g (f x) == x
        g-f x = idp

  iso≃id : {G H : Group {α}} → (G ≃ᴳ H) ≃ (G == H)
  iso≃id {G} {H} =
      G ≃ᴳ H
    ≃⟨ iso≃group'= G H ⟩
      group'= Σ⟪ G ⟫ Σ⟪ H ⟫
    ≃⟨ magma=-equiv (Group.M G) (Group.M H) ⟩
      Group.M G == Group.M H
    ≃⟨ {!   !} ⟩ -- this should follow from the fact that is-group-is-prop
      Σ⟪ G ⟫ == Σ⟪ H ⟫
    ≃⟨ ap-equiv (Group≃Group' ⁻¹) Σ⟪ G ⟫ Σ⟪ H ⟫ ⟩
      G == H
    ≃∎
