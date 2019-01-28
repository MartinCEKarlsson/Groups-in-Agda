{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.NType
open import lib.Funext
open import lib.types.Pi
open import Group-basics


{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal {α : ULevel} where

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {G H : Group {α}} (p : G == H) → (Subgrp G) → (Subgrp H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
idtoiso {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {G H : Group {α}} (p : G == H) → (Subgrp G) → (Subgrp H)
idtoiso-subgrp {G} {.G} idp G' = G' -- We can actually just case split!
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
trans-equiv-idtoiso : (G H : Group) → transp-subgrp {G} {H} == idtoiso-subgrp {G} {H}
trans-equiv-idtoiso G H = λ= (λ {idp → idp})

-- (transport Subgroup p (f G)) == f G

! : {α : ULevel} {X : Type α} {x y : X} (p : x == y) → y == x
! idp = idp

apd2 : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd2 f idp = idp

map-lift2 : {G : Group} {H : Group} (hom : H →ᴳ G) → (Subgrp G → Subgrp  H)
map-lift2 {G} {H} hom sub-g = record { prop = prop-lemma  ; f = λ {a} → f-lemma a ; id =  id-lemma ; comp =  λ {a} {b} → comp-lemma a b; inv = λ {a} → inv-lemma a}
  where
    open Subgrp sub-g
    open GroupHom hom renaming (f to h-to-g)

    prop-lemma : Group.U H → Set α
    prop-lemma h = prop (h-to-g h)

    f-lemma :  (a : Group.U H) → is-prop (prop-lemma a)
    f-lemma a = f

    id-lemma : prop-lemma (Group.e H)
    id-lemma = coe (ap prop (! id-to-id)) id

    comp-lemma : (a b : Group.U H) → prop-lemma a → prop-lemma b → prop-lemma (Group.comp H a b)
    comp-lemma a b prop-a prop-b = coe (ap prop (! (pres-comp a b))) (comp prop-a prop-b)

    inv-lemma : (a : Group.U H) → prop (h-to-g a) → prop (h-to-g (Group.i H a))
    inv-lemma a prop-a = coe (ap prop (! (pres-i a))) (inv prop-a)

map-lift : {G : Group} {H : Group} (iso : G ≃ᴳ H) → (Subgrp G → Subgrp  H)
map-lift {G} {H} iso sub-g = map-lift2 {G} {H} hom sub-g
  where
    hom : H →ᴳ G
    hom = _≃ᴳ_.g-hom iso


postulate
  isotoid : {G H : Group {α}} (iso : G ≃ᴳ H) → G == H
  iso-id-equiv : {G H : Group {α}} (iso : G ≃ᴳ H) → (idtoiso (isotoid iso)) == iso
  --some-lemma : {G H : Group} (f : (I : Group) → (Subgrp I)) (iso : H ≃ᴳ G) → ((map-lift (Σ.fst iso) (f G)) == f H)


funqeq : {β : ULevel} {A B : Set β} {f g : A → B} (p : f == g) (a : A) → (f a == g a)
funqeq idp a = idp

prop= : {G : Group {α}} (N M : Subgrp G) → Set (lsucc α)
prop= N M =  (Subgrp.prop N) == (Subgrp.prop M)

impl-to-expl : {β : ULevel} {A : Type α} {B : A → Type β} → (f : ({a : A} → B a)) → ((a : A) → B a)
impl-to-expl f = –> expose-equiv f

expl-to-impl : {β : ULevel} {A : Type α} {B : A → Type β} → (f : ((a : A) → B a)) → ({a : A} → B a)
expl-to-impl f {a} = f a

λ=-implicit : {β : ULevel} {A : Type α} {B : A → Type β} → {f g : ({a : A} → B a)} → ((a : A) → (f {a} == g {a})) → ((λ {x} → f {x}) == (λ {x} → g {x}))
λ=-implicit ext = ap expl-to-impl (λ= ext)

subgrp= : {G : Group {α}} {N M : Subgrp G} (eq : prop= N M) → (N == M)
subgrp= eq = {!!}

module Subgrp-encode-code {G : Group {α}} where

  encode : (N M : Subgrp G) (eq : prop= N M) → (N == M)
  encode record { prop = prop ; f = f ; id = id ; comp = comp ; inv = inv } record { prop = .prop ; f = f₁ ; id = id₁ ; comp = comp₁ ; inv = inv₁ } idp = {!!}
    where
      id= : id == id₁
      id= = prop-path f id id₁

      f= : f == f₁
      f= = {!!}

      comp= : comp == comp₁
      comp= = {!!}  -- We need to use a version of implicit function extensionality here, it is proved above but not working in this context yet. 
  
      inv= : inv == inv₁
      inv= = {!!}


module definable-normal-proof  (f : (G : Group) → (Subgrp G)) where

  map-lift-path-lemma : {G H : Group} (p : G == H) → (map-lift (idtoiso p)) == (transport Subgrp  p)
  map-lift-path-lemma idp = λ= (λ g → subgrp= idp)

  map-lift-lemma : {G : Group} (aut : G ≃ᴳ G) → map-lift aut == transport Subgrp (isotoid aut)
  map-lift-lemma aut =
      map-lift aut =⟨ ap map-lift (! (iso-id-equiv aut)) ⟩
      map-lift (idtoiso (isotoid aut)) =⟨ map-lift-path-lemma ((isotoid aut)) ⟩
      transport Subgrp (isotoid aut) =∎

  final-result : {G : Group} (aut : G ≃ᴳ G) → ((map-lift aut (f G)) == f G)
  final-result {G} aut =  funqeq (map-lift-lemma aut) (f G) ∙ (apd2 f (isotoid aut))




{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : (f : (G : Group {α}) → (Subgrp G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
