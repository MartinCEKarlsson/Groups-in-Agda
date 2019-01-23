{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences2
open import Eq-reasoning
open import Group

{-- in this file we formalize subgroups and normal subgroups --}


record is-subgroup {ℓ} (G : Group ℓ) : Set ((lsucc ℓ))  where
  private
    module G = Group.Group G
  field
    prop : G.U → Set ℓ
    level : ∀ {g : G.U} → is-hprop (prop g)
    -- In theory being inhabited implies that the identity is included,
    -- but in practice let's just prove the identity case.
    ident : prop G.e
    diff : ∀ {g₁ g₂ : G.U} → prop g₁ → prop g₂ → prop (G.comp g₁ g₂)
