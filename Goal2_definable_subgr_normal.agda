{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Funext

open import Eq-reasoning
open import Group-basics


{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal where

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {α β : ULevel} {G H : Group} (p : G == H) → (Subgrp {α} {β} G) → (Subgrp H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : {α : ULevel} {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
idtoiso {α} {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {α β : ULevel} {G H : Group} (p : G == H) → (Subgrp {α} {β} G) → (Subgrp {_} {β} H)
idtoiso-subgrp {α} {β} {G} {.G} idp G' = G' -- We can actually just case split!
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
trans-equiv-idtoiso : {α β : ULevel} (G H : Group) → transp-subgrp {α} {β} {G} {H} == idtoiso-subgrp {α} {β} {G} {H}
trans-equiv-idtoiso G H = λ= (λ {idp → idp})

-- (transport Subgroup p (f G)) == f G

map-lift : {α β γ δ : ULevel} {G : Group} {H : Group} (f : G →ᴳ H) → (Subgrp {α} {γ} G → Subgrp {β} {δ} H)
map-lift f subg = record { prop = {! !} ; f = {! !} ; id = {! !} ; comp = {! !} }

postulate
  iso-implies-path : {α : ULevel} {G H : Group {α}} (iso : G ≃ᴳ H) → G == H

module definable-normal-proof  {α β : ULevel} (f : (G : Group) → (Subgrp {α} {β} G)) where

  cool-lemma : {G : Group} (aut : G ≃ᴳ G) → ((map-lift (fst aut) (f G)) == f G)
  cool-lemma aut =  {! !} ∙ {!   !} -- apd f (iso-implies-path aut)

  new-goal : {G : Group}(aut : G ≃ᴳ G) → map-lift (Σ.fst aut) == transport Subgrp (iso-implies-path aut)
  new-goal aut = {! !}


{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : {α β : ULevel} (f : (G : Group) → (Subgrp {α} {β} G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
