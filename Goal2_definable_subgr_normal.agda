{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.NType
open import lib.NType2
open import lib.Funext
open import lib.types.Pi
open import lib.PathGroupoid
open import Group-basics


{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal {α : ULevel} where

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
idtoiso {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)


{- In this module, we define a function that given an isomorphism between G and H and a subgroup
   of type G, transforms it into a subgroup of type H -}
module _ {G : Group} {H : Group} where
  lift-hom-over-subgrp : (hom : H →ᴳ G) → (Subgrp G → Subgrp  H)
  lift-hom-over-subgrp hom sub-g = record { prop = prop-lemma  ; f = λ {a} → f-lemma a ; id =  id-lemma ; comp =  λ {a} {b} → comp-lemma a b; inv = λ {a} → inv-lemma a}
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

  lift-iso-over-subgrp : (iso : G ≃ᴳ H) → (Subgrp G → Subgrp  H)
  lift-iso-over-subgrp iso sub-g = lift-hom-over-subgrp hom sub-g
    where
      hom : H →ᴳ G
      hom = _≃ᴳ_.g-hom iso


postulate
  isotoid : {G H : Group {α}} (iso : G ≃ᴳ H) → G == H
  iso-id-equiv : {G H : Group {α}} (iso : G ≃ᴳ H) → (idtoiso (isotoid iso)) == iso
  --some-lemma : {G H : Group} (f : (I : Group) → (Subgrp I)) (iso : H ≃ᴳ G) → ((map-lift (Σ.fst iso) (f G)) == f H)


funqeq : {β : ULevel} {A B : Set β} {f g : A → B} (p : f == g) (a : A) → (f a == g a)
funqeq idp a = idp

module _ where

  private
    {- First, we give an alternative definition of a subgroup -}
    record is-subgrp {G : Group {α}} (prop : (Group.U G) → Set α) : Set (lsucc α) where
      private
        module G = Group G
      field
        f : ∀ (a : G.U) → is-prop( prop a)
        id : prop G.e
        comp : ∀ (a b : G.U) → prop a → prop b → prop (G.comp a b)
        inv : ∀ (a : G.U) → prop a → prop (G.i a)

    subgrp' : {G : Group {α}} → Set (lsucc α)
    subgrp' {G} = Σ (Group.U G → Set α) (λ y → is-subgrp {G} y)

    is-prop-is-prop : {ℓ : ULevel} {X : Set ℓ} → (is-prop (is-prop X))
    is-prop-is-prop = has-level-is-prop

    any-isg-with-same-prop-are-equal : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) → (isg1 == isg2)
    any-isg-with-same-prop-are-equal {G} isg1 isg2 = =lemma isg1 isg2 f-eq id-eq comp-eq inv-eq
      where
        open is-subgrp
        f-eq : f isg1 == f isg2
        f-eq = λ= (λ a → prop-path is-prop-is-prop (f isg1 a) (f isg2 a))

        id-eq : id isg1 == id isg2
        id-eq = prop-path (f isg1 (Group.e G)) (id isg1) (id isg2)

        comp-eq : comp isg1 == comp isg2
        comp-eq = λ= (λ a → λ= (λ b → λ= (λ x → λ= λ y → prop-path (f isg1 (Group.comp G a b)) (comp isg1 a b x y) (comp isg2 a b x y))))

        inv-eq : inv isg1 == inv isg2
        inv-eq = λ= (λ a → λ= (λ b → prop-path (f isg1 (Group.i G a)) (inv isg1 a b) (inv isg2 a b)))

        =lemma : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) (eq1 : f isg1 == f isg2) (eq2 : id isg1 == id isg2) (eq3 : comp isg1 == comp isg2) (eq4 : inv isg1 == inv isg2) → (isg1 == isg2)
        =lemma record { f = .(f isg2) ; id = .(id isg2) ; comp = .(comp isg2) ; inv = .(inv isg2) } isg2 idp idp idp idp = idp

    path-prop-implies-path-isg : {G : Group {α}} (pr1 pr2 : (Group.U G) → Set α) (p : pr1 == pr2) (subgr1 : is-subgrp {G} pr1) (subgr2 : is-subgrp {G} pr2) → (transport is-subgrp p subgr1 == subgr2)
    path-prop-implies-path-isg pr1 pr2 p subgr1 subgr2 = any-isg-with-same-prop-are-equal (transport is-subgrp p subgr1) subgr2

    subgrp'= : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) (pt : (transport is-subgrp p (Σ.snd a)) == (Σ.snd b)) → (a == b)
    subgrp'= (fst₁ , snd₁) (.fst₁ , .snd₁) idp idp = idp

    subgrp'-eq : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) → (a == b)
    subgrp'-eq a b p = subgrp'= a b p (path-prop-implies-path-isg (Σ.fst a) (Σ.fst b) p (Σ.snd a) (Σ.snd b))

    subgrp-subgrp'-equiv : (G : Group {α}) → Subgrp G ≃ subgrp' {G}
    subgrp-subgrp'-equiv G = f , (record { g = g ; f-g = f-g ; g-f = g-f ; adj = λ a → idp })
      where
        f : Subgrp G → subgrp' {G}
        f record { prop = prop ; f = f ; id = id ; comp = comp ; inv = inv } = prop , record {f = λ a → f {a} ; id = id; comp = λ a b → comp {a} {b}; inv = λ a → inv {a}}

        g : subgrp' {G} → Subgrp G
        g (prop , record { f = f ; id = id ; comp = comp ; inv = inv }) = record{ prop = prop ; f = λ {a} → f a ; id = id ; comp = λ {a} {b} → comp a b ; inv = λ {a} → inv a}

        f-g : (b : subgrp') → f (g b) == b
        f-g b = idp

        g-f : (a : Subgrp G) → g (f a) == a
        g-f a = idp

  subgrp-eq : {G : Group {α}} {a b : Subgrp G} (p : Subgrp.prop a == Subgrp.prop b) → (a == b)
  subgrp-eq {G} {a} {b} p = path
    where
      open is-equiv (Σ.snd (subgrp-subgrp'-equiv G))
      f : Subgrp G → subgrp' {G}
      f = Σ.fst (subgrp-subgrp'-equiv G)

      prf : ((f a) == (f b))
      prf = subgrp'-eq (f a) (f b) p

      path : (a == b)
      path =
        a  =⟨ ! (g-f a) ⟩
        g(f(a)) =⟨ ap g prf ⟩
        g(f(b)) =⟨ g-f b ⟩
        b =∎


apd2 : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd2 f idp = idp

{- We show in this module that if you have a map f from groups to subgroups, a particular
   group G and any automorphism between G, then there is a path between the subgroup (f G)
   and the subgroup obtained by applying that automorphism to (f G) -}
module _  (f : (G : Group {α}) → (Subgrp G)) where

  private
    lift-aut-lemma1 : {G H : Group} (p : G == H) → (lift-iso-over-subgrp (idtoiso p)) == (transport Subgrp  p)
    lift-aut-lemma1 idp = λ= (λ g → subgrp-eq idp)

    lift-aut-lemma2 : {G : Group} (aut : G ≃ᴳ G) → lift-iso-over-subgrp aut == transport Subgrp (isotoid aut)
    lift-aut-lemma2 aut =
        lift-iso-over-subgrp aut =⟨ ap lift-iso-over-subgrp (! (iso-id-equiv aut)) ⟩
        lift-iso-over-subgrp (idtoiso (isotoid aut)) =⟨ lift-aut-lemma1 ((isotoid aut)) ⟩
        transport Subgrp (isotoid aut) =∎

  lift-aut-retains-subgrp : {G : Group} (aut : G ≃ᴳ G) → ((lift-iso-over-subgrp aut (f G)) == f G)
  lift-aut-retains-subgrp {G} aut =  funqeq (lift-aut-lemma2 aut) (f G) ∙ (apd2 f (isotoid aut))




{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : (f : (G : Group {α}) → (Subgrp G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
