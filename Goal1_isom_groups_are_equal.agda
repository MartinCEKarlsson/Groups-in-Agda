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

open import Group-basics
open import Magma

module Goal1_isom_groups_are_equal where

{- In this file we work towards the first goal of the project: isomorphic groups are equal in HoTT -}

isotoid : {α : ULevel} {G H : Group {α}} (iso : G ≃ᴳ H) → G == H
isotoid {α} {G} {H} = {!   !}
  where
  {- We want the proofs that a Magma is a group to be propositions. -}
  is-group-is-prop : {G : Magma} → is-prop (is-group G)
  is-group-is-prop {M} = all-paths-is-prop lemma
    where
      open Magma.Magma M
      lemma : (x y : is-group M) → (x == y)
      lemma (isAssoc , isSet , (e , isUnit) , inv , isInv)
            (isAssoc' , isSet' , (e' , isUnit') , inv' , isInv')
            =   pair×= isAssoc= (pair×= isSet= (pair= unit= ↓-inv=))
        where
          module G = Group (group M (isAssoc , isSet , (e , isUnit) , inv , isInv))
          module H = Group (group M (isAssoc' , isSet' , (e' , isUnit') , inv' , isInv'))

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
            prop-path paths-are-props ((transport ((λ x → is-unit-l _∗_ x)) e= isUnit) x) (isUnit' x)))

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

          isInv= : transport (λ x → is-inverse-l _∗_ x inv')
                             (e=)
                             (transport (λ x → is-inverse-l _∗_ e x)
                                        (inv=)
                                        isInv)
                   == isInv'
          isInv= = λ= {α} (λ x → prop-path paths-are-props (transport
            (λ x → is-inverse-l _∗_ x inv') (e=) (transport
              (λ x → is-inverse-l _∗_ e x) (inv=) isInv) x) (isInv' x))

          ↓-inv= : (inv , isInv) == (inv' , isInv') [ (λ { (x , isU) → has-inverse-l _∗_ x}) ↓ unit= ]
          ↓-inv= = {!   !} -- from-transp (λ x → has-inverse-l _∗_ (fst x)) unit=
                   -- {{! !}}
                   -- (pair= inv= (from-transp (λ x → is-inverse-l _∗_ e' x) inv= isInv=))
