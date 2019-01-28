{-# OPTIONS --without-K --rewriting #-}
open import Magma-basics

open import lib.Equivalence
open import lib.Base
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Sigma
open import Group-basics

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
