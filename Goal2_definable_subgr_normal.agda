{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.NType

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

! : {α : ULevel} {X : Type α} {x y : X} (p : x == y) → y == x
! idp = idp

apd2 : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd2 f idp = idp

map-lift : {α γ : ULevel} {G : Group} {H : Group} (hom : H →ᴳ G) → (Subgrp {α} {γ} G → Subgrp {α} {γ} H)
map-lift {α} {γ} {G} {H} hom sub-g = record { prop = prop-lemma  ; f = λ {a} → f-lemma a ; id =  id-lemma ; comp =  λ {a} {b} → comp-lemma a b; inv = {!!}}
  where
    open Subgrp sub-g
    open GroupHom hom renaming (f to h-to-g)

    prop-lemma : Group.U H → Set γ
    prop-lemma h = prop (h-to-g h)

    f-lemma :  (a : Group.U H) → is-prop (prop-lemma a)
    f-lemma a = f

    id-lemma : prop-lemma (Group.e H)
    id-lemma = coe (ap prop (! id-to-id)) id

    comp-lemma : (a b : Group.U H) → prop-lemma a → prop-lemma b → prop-lemma (Group.comp H a b)
    comp-lemma a b prop-a prop-b = coe (ap prop (! (pres-comp a b))) (comp prop-a prop-b)

    inv-lemma : (a : Group.U H) → prop (h-to-g a) → prop (h-to-g (Group.i H a))
    inv-lemma a prop-a = coe (ap prop (! (pres-i a))) (inv prop-a)


postulate
  iso-implies-path : {α : ULevel} {G H : Group {α}} (iso : G ≃ᴳ H) → G == H


module definable-normal-proof  {α β : ULevel} (f : (G : Group) → (Subgrp {α} {β} G)) where

  cool-lemma : {G : Group} (aut : G ≃ᴳ G) → ((map-lift (Σ.fst aut) (f G)) == f G)
  cool-lemma aut =  {! !} ∙ (apd2 f (iso-implies-path aut)) -- apd f (iso-implies-path aut)

  --new-goal : {G : Group}(aut : G ≃ᴳ G) → map-lift aut == transport Subgrp (iso-implies-path aut)
  --new-goal aut = {! !}


{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : {α β : ULevel} (f : (G : Group) → (Subgrp {α} {β} G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
