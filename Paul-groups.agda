{-# OPTIONS --without-K --rewriting #-}
open import Magma-basics

open import lib.Equivalence
open import lib.Base
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Sigma
open import lib.Univalence
open import lib.Funext
open import lib.types.Pi
open import Group-basics
open import Goal1_isom_groups_are_equal

{- I made this file to experiment a bit with the definitions, library, and univalence for groups -}

module Paul-groups {ℓ : ULevel} where

{- We give an alternative definition of a group, and prove -}

record Group' : Type (lsucc ℓ) where  -- conditions for a Magma to be a group

  field
    M : Magma {ℓ}

  open Magma M

  U : Type ℓ
  U = X

  comp : U → U → U
  comp a b = a ∗ b

  _·_ = comp

  field
    e : X --identity
    i : X → X --inverse
    ass : (a b c : X) → ((a · b) · c) == (a · (b · c))
    unit-l : (a : X) → (e · a) == a
    inv-l : (a : X) → ((i a) · a) == e
    set : is-set X

  abstract
    congr : {a b c d : U} → (a == c) → (b == d) → (a · b) == (c · d)
    congr idp idp = idp

    inv-r : (a : U) → (a · (i a)) == e
    inv-r a =
      a · (i a) =⟨ ! (unit-l (a · (i a))) ⟩
      e · (a · (i a)) =⟨ ap (λ y → (y · (a · (i a)))) (! (inv-l (i a)))  ⟩
      ( (i (i a)) · (i a) ) · (a · (i a)) =⟨ ass (i (i a)) (i a) (a · (i a)) ⟩
      (i (i a)) · ( (i a) · (a · (i a)) ) =⟨ congr idp (! (ass (i a) a (i a))) ⟩
      (i (i a)) · ( ((i a) · a) · (i a) ) =⟨ congr idp (congr (inv-l a) idp) ⟩
      (i (i a)) · (e · (i a)) =⟨ congr idp (unit-l (i a)) ⟩
      (i (i a)) · (i a) =⟨ inv-l (i a) ⟩
      e =∎

    unit-r : (a : U) → (a · e) == a
    unit-r a =
      a · e =⟨ congr idp (! (inv-l a)) ⟩
      a · ((i a) · a) =⟨ ! (ass a (i a) a) ⟩
      (a · (i a)) · a =⟨ congr (inv-r a) idp ⟩
      e · a =⟨ unit-l a ⟩
      a =∎

{- In the following module we prove some basic lemma's of groups -}
module _ {G : Group'} where
  open Group' G

  comp-is-congr : {a b c d : U} → (a == c) → (b == d) → (a · b) == (c · d)
  comp-is-congr idp idp = idp

  solve-eq : (a x b : U) → (a · x) == b → x == ((i a) · b)
  solve-eq a x b p =
    x =⟨ ! (unit-l x) ⟩
    e · x =⟨ congr (! (inv-l a)) idp ⟩
    ((i a) · a) · x =⟨ ass (i a) a x ⟩
    (i a) · (a · x) =⟨ congr idp p ⟩
    (i a) · b =∎

  unique-solve : (a b x y : U) → (a · x) == b → (a · y) == b → x == y
  unique-solve a b x y p q =
    x =⟨ solve-eq a x b p ⟩
    (i a) · b =⟨ ! (solve-eq a y b q) ⟩
    y =∎

{- We prove that Group and Group' are equivalent -}
group-equiv : Group {ℓ} ≃ Group'
group-equiv = equiv f g f-g g-f
  where
    f : Group {ℓ} → Group'
    f G = record
            { M = M
            ; e = e
            ; i = i
            ; ass = associative
            ; unit-l = unit-l
            ; inv-l = inv-l
            ; set = set
            }
      where
        open Group G

    g : Group' → Group {ℓ}
    g G = group (M) ((ass) , ((set) , (((e) , unit-l) , i , (λ a → inv-l a))))
      where
        open Group' G

    f-g : (G : Group') → (f (g G) == G)
    f-g G = idp

    g-f : (G : Group {ℓ}) → (g (f G) == G)
    g-f G = idp

{- We define when two groups should be equal/isomorphic, namely if their underlying magma's are equal/isomorphic -}
group= : (G H : Group') → Type ℓ
group= G H = magma= (Group'.M G) (Group'.M H)

_≅_ = group=  -- We use ≅ for group isomorphism, whereas ≃ means equivalence as usual.

{- Underlying map of the isomorphism -}
iso-map : {G H : Group'} → (G ≅ H) → (Group'.U G → Group'.U H)
iso-map iso = –> (magma=.carrier-equiv iso)

{- Inverse map of the ismorphism -}
iso-map-inv : {G H : Group'} → (G ≅ H) → (Group'.U H → Group'.U G)
iso-map-inv iso = <– (magma=.carrier-equiv iso)

{- We prove some facts about isomorphisms -}
module _≅_ {G H : Group'} (iso : G ≅ H) where
  module G = Group' G
  module H = Group' H

  open Group' G renaming (comp to _·ᴳ_)
  open Group' H renaming (comp to _·ᴴ_)

  f : G.U → H.U
  f = iso-map {G} {H} iso

  g : H.U → G.U
  g = iso-map-inv {G} {H} iso

  f-g : (a : H.U) → f (g a) == a
  f-g = is-equiv.f-g (snd (magma=.carrier-equiv iso))

  g-f : (a : G.U) → g (f a) == a
  g-f = is-equiv.g-f (snd (magma=.carrier-equiv iso))

  preserves-comp : (a b : G.U) → f (a ·ᴳ b) == ((f a) ·ᴴ (f b))
  preserves-comp a b = magma=.preserves-operator iso a b

  preserves-comp-inv : (a b : H.U) → g (a ·ᴴ b) == ((g a) ·ᴳ (g b))
  preserves-comp-inv a b =
    g (a ·ᴴ b) =⟨ ap g (comp-is-congr {H} (! (f-g a))  (! (f-g b))) ⟩
    g ( f (g a) ·ᴴ f (g b) ) =⟨ ap g (! (preserves-comp (g a) (g b))) ⟩
    g ( f ( (g a) ·ᴳ (g b) ) ) =⟨ g-f ((g a) ·ᴳ (g b)) ⟩
    ((g a) ·ᴳ (g b)) =∎

  reflexive : (H ≅ G)
  reflexive = record { carrier-equiv = g , (record { g = f ; f-g = g-f ; g-f = f-g ; adj = is-equiv.adj' (snd (magma=.carrier-equiv iso)) }) ; preserves-operator = preserves-comp-inv }

  preserves-unit : f G.e == H.e
  preserves-unit = unique-solve {H} (f G.e) (f G.e) (f G.e) H.e lemma (H.unit-r (f G.e))
    where
      lemma : (f G.e ·ᴴ f G.e) == f G.e
      lemma =
        (f G.e) ·ᴴ (f G.e) =⟨ ! (preserves-comp G.e G.e) ⟩
        f (G.e ·ᴳ G.e) =⟨ ap f (G.unit-l G.e) ⟩
        f G.e =∎

  preserves-inv : (a : G.U) → f (G.i a) == H.i (f a)
  preserves-inv a = unique-solve {H} (f a) H.e (f (G.i a)) (H.i (f a)) lemma (H.inv-r (f a))
    where
      lemma : ((f a) ·ᴴ (f (G.i a))) == H.e
      lemma =
        ((f a) ·ᴴ (f (G.i a))) =⟨ ! (preserves-comp a (G.i a)) ⟩
        f (a ·ᴳ (G.i a)) =⟨ ap f (G.inv-r a) ⟩
        f (G.e) =⟨ preserves-unit ⟩
        H.e =∎


{- Goal 1 of the project is to prove that isomorphic groups are equal -}
group=-equiv : (G H : Group') → (G ≅ H) → (G == H)
group=-equiv G H is = {! !}


{- Goal 2 of the project is to prove that definable subgroups are normal -}

{- Step 1 : define the map-lift and the idtoiso function that we want -}
idtoiso' : {G H : Group {ℓ}} → G == H → G ≃ᴳ H
idtoiso' idp = (group-hom (coe idp) (λ g₁ g₂ → idp)) , record { g = λ x → x ; f-g = λ b → idp ; g-f = λ a → idp ; adj = λ a → idp }

correct-function : {G H : Group {ℓ}} → (idtoiso {ℓ} {G} {H} == idtoiso' {G} {H})
correct-function = λ= (λ x → {!!})

map-lift : {α : ULevel} {G H : Group {α}} → (G ≃ᴳ H) → Subgrp G → Subgrp H
map-lift {α} {G} {H} iso G' = record { prop = propᴴ ; f = is-prop-G' ; id = id-prop ; comp = comp-lemma ; inv = inv-lemma }
  where 
    open _≃ᴳ_ iso
    open Subgrp G' renaming (prop to propᴳ)
    module G = Group G
    module H = Group H
  
    inverse-hom : H →ᴳ G 
    inverse-hom = _≃ᴳ_.g-hom iso

    inverse-map : H.U → G.U
    inverse-map = GroupHom.f inverse-hom

    propᴴ : H.U → Set α
    propᴴ = propᴳ ∘ inverse-map

    is-prop-G' : ∀ {a : H.U} → is-prop (propᴴ a)
    is-prop-G' {a} = f

    id-prop : propᴴ H.e
    id-prop = coe (ap propᴳ (! (GroupHom.id-to-id inverse-hom))) id

    comp-lemma : {a b : H.U} → propᴴ a → propᴴ b → propᴴ (H.comp a b)
    comp-lemma {a} {b} aprop bprop = coe (ap propᴳ (! (preserves-comp a b))) (comp aprop bprop)

    inv-lemma : {a : H.U} → propᴴ a → propᴴ (H.i a)
    inv-lemma {a} aprop = coe (ap propᴳ (! (GroupHom.pres-i inverse-hom a))) (inv aprop)

{- Step 2 : prove a general lemma about lifting the idtoiso function, namely that it characterises the transport lifting -}
prop= : {G : Group {ℓ}} (N M : Subgrp G) → Set (lsucc ℓ)
prop= N M = Subgrp.prop N == Subgrp.prop M

{- We need this help functions to switch between implicit and explicit functions to use function extensionality -}
module _ {β : ULevel} {A : Type ℓ} {B : A → Type β} where
  impl-to-expl : (f : ({a : A} → B a)) → ((a : A) → B a)
  impl-to-expl f = –> expose-equiv f

  expl-to-impl : (f : ((a : A) → B a)) → ({a : A} → B a)
  expl-to-impl f = {!!}

  imp-exp-inv : (f : {a : A} → B a) → (expl-to-impl (impl-to-expl f) == f)
  imp-exp-inv f = idp

{- Lemma : is-prop is a prop -}
!-cancel-l : {X : Set ℓ} {x y : X} (p q : x == y) → (p ∙ ((! p) ∙ q) == q)
!-cancel-l p idp =
  p ∙ ((! p) ∙ idp) =⟨ ! (∙-assoc p (! p) idp) ⟩
  (p ∙ (! p)) ∙ idp =⟨ ap (λ x → x ∙ idp) (!-inv-r p) ⟩
  idp ∙ idp =⟨ idp ⟩
  idp =∎

prop-lemma : {X : Set ℓ} (f : is-prop X) (x y : X) (p : x == y) → (prop-path f x y == p)
prop-lemma {X} f x y p = lemma2 ∙ !-cancel-l (prop-path f x y) p
  where
    {- The two useful lemmas have been put here as local definitions using the where keyword
       above. This ensures that we can use the same names lemma1 and lemma2 again elsewhere
       without getting any conflicts.
    -}
    lemma1 : (z : X) (q : y == z) → (prop-path f x z == prop-path f x y ∙ q)
    lemma1 z idp = ! (∙-unit-r (prop-path f x y))

    lemma2 : (prop-path f x y == prop-path f x y ∙ (! (prop-path f x y) ∙ p))
    lemma2 = lemma1 y (! (prop-path f x y) ∙ p)

is-prop-prop-path : {X : Set ℓ} → (x y : is-prop X) → (x == y)
is-prop-prop-path (has-level-in has-level-apply₁) (has-level-in has-level-apply₂) = {!!}

has-all-paths-has-all-paths : {X : Set ℓ} → (has-all-paths (has-all-paths X))
has-all-paths-has-all-paths = λ f g → λ= (λ x → λ= (λ y → ! (prop-lemma (all-paths-is-prop f) x y (f x y)) ∙ prop-lemma (all-paths-is-prop f) x y (g x y)))

is-prop-has-all-paths : {X : Set ℓ} → (is-prop (has-all-paths X))
is-prop-has-all-paths = all-paths-is-prop has-all-paths-has-all-paths

has-all-paths-is-prop : {X : Set ℓ} → (has-all-paths (is-prop X))
has-all-paths-is-prop = λ x y → {!!}

paths-are-props : {X : Set ℓ} {a b : X} → (isSet : is-set X) → is-prop (a == b)
paths-are-props {X} {a} {b} isSet = has-level-apply isSet a b

prop-is-prop : {X : Set ℓ} → (isSet : is-set X) → (is-prop (is-prop X))
prop-is-prop isSet = {!!}

is-prop-is-prop : {X : Set ℓ} → (is-prop (is-prop X))
is-prop-is-prop = {!!}

{- implicit function extensionality -}
λ=-implicit : {β : ULevel} {A : Set ℓ} {B : A → Set β} → (f g : ({x : A} → (B x))) → ((x : A) → ((f {x}) == (g {x}))) → (f == g)
λ=-implicit f g p = {!!}

{- Lemma: two subgroups are equal if their props are equal -}
subgrp= : {G : Group {ℓ}} {M N : Subgrp G} (eq : prop= N M) → (M == N)
subgrp= {G} {M = record { prop = propᴹ ; f = fᴹ ; id = idᴹ ; comp = compᴹ ; inv = invᴹ }} {N = record { prop = .propᴹ ; f = fᴺ ; id = idᴺ ; comp = compᴺ ; inv = invᴺ }} idp = {!!}
  where
    f-lemma : fᴹ == fᴺ
    f-lemma = prop-path is-prop-is-prop fᴹ fᴺ

    id-lemma : idᴹ == idᴺ
    id-lemma = prop-path fᴹ idᴹ idᴺ

    comp-lemma : compᴹ == compᴺ
    comp-lemma = λ= (λ x → λ= (λ y → prop-path fᴹ (compᴹ x y) (compᴺ x y)))

    inv-lemma : invᴹ == invᴺ
    inv-lemma = λ= (λ x → prop-path fᴹ (invᴹ x) {!invᴺ x!})
  
    f-lemma-1 : (–> expose-equiv fᴹ == –> expose-equiv fᴺ)
    f-lemma-1 = λ= (λ a → prop-path is-prop-is-prop ((–> expose-equiv fᴹ) a) ((–> expose-equiv fᴺ) a))

    --f-lemma-2 : expl-to-impl (impl-to-expl fᴹ) == expl-to-impl (impl-to-expl fᴺ)
    f-lemma-2 : fᴹ == fᴺ
    f-lemma-2 =
      fᴹ =⟨ {!!} ⟩
      g (f fᴹ) =⟨ {!!} ⟩
      g (f fᴺ) =⟨ {!!} ⟩
      fᴺ =∎
        where
          f = fst expose-equiv
          g = is-equiv.g (snd expose-equiv)
          f-g = is-equiv.f-g (snd expose-equiv)
          g-f = is-equiv.g-f (snd expose-equiv)

trans-to-idtoiso-lift : {G H : Group {ℓ}} (p : G == H) → ((transport Subgrp p) == (map-lift (idtoiso' p)))
trans-to-idtoiso-lift idp = λ= (λ G' → subgrp= idp)

    

{- Final goal: -}
def-subgroups-are-normal : (f : (G : Group {ℓ}) → (Subgrp G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!  !}
