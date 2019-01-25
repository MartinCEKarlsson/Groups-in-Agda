{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences
open import Eq-reasoning
open import SetsAndProps
open import Group-basics


{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal where

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : ∀ {i} {G H : Group i} → (G == H) → (G ≃ᴳ H)
idtoiso {i} {G} {.G} idp = →ᴳ-id , (λ y → build-is-contr (y , idp) (λ {(x , idp) → idp}))

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
idtoiso-subgrp {i} {G} {.G} idp G' = G' -- We can actually just case split!
-- idtoiso-subgrp {i} {G} {H} p G' = record { prop = λ x → Subgrp.prop G' (θ-inv(x)) ; f = Subgrp.f G' ; id = {! !} ; comp = {! p  !} }
  -- where
  --   module H = Group H
  --   module G = Group G
  --
  --   equiv : (G ≃ᴳ H) -- The equivalence
  --   equiv = idtoiso p
  --
  --   open GroupHom (Σ.fst equiv)
  --
  --   θ : (G.U → H.U)   -- The forward map of the equivalence
  --   θ = GroupHom.f (Σ.fst equiv)
  --
  --   open is-hae (is-equiv→is-hae θ (Σ.snd equiv))
  --
  --   θ-inv : (H.U → G.U)  -- The backward map of the equivalence
  --   θ-inv = g

{- We want to prove that the previous two functions Subgrp G → Subgrp H are homotopic -}
trans-equiv-idtoiso : {i : ULevel} (G H : Group i) → transp-subgrp {i} {G} {H} == idtoiso-subgrp {i} {G} {H}
trans-equiv-idtoiso {i} G H = funext transp-subgrp idtoiso-subgrp (λ {idp → idp})


apd : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd f idp = idp

--(transport Subgroup p (f G)) == f G

map-lift : {l k : ULevel} {G : Group l} {H : Group k} (f : G →ᴳ H) → (Subgrp {l} {l} G → Subgrp {k} {k} H)
map-lift f subg = record { prop = {!!} ; f = {!!} ; id = {!!} ; comp = {!!} }

postulate
  iso-implies-path : {l : ULevel}{G H : Group l} (iso : G ≃ᴳ H) → G == H

module definable-normal-proof {ℓ : ULevel} (f : (G : Group ℓ) → (Subgrp {ℓ} {ℓ} G)) where

  cool-lemma : {G : Group ℓ} (aut : G ≃ᴳ G) → ((map-lift (Σ.fst aut) (f G)) == f G)
  cool-lemma aut =  {!!} ∙ apd f (iso-implies-path aut)

  new-goal : {G : Group ℓ}(aut : G ≃ᴳ G) → map-lift (Σ.fst aut) == transport Subgrp (iso-implies-path aut)
  new-goal aut = {!!}


{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : {ℓ : ULevel} (f : (G : Group ℓ) → (Subgrp {ℓ} {ℓ} G)) → (H : Group ℓ) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
