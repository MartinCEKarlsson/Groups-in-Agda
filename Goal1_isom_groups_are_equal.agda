{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences
open import Eq-reasoning
open import SetsAndProps
open import Group-basics

module Goal1_isom_groups_are_equal where

{- In this file we work towards the first goal of the project: isomorphic groups are equal in HoTT -}

{- We want some sort of convenient equivalence for is-group records. -}
module is-group-encode-decode {α : ULevel} {X : Set α} where
  module is-group-eq-transports {G H : is-group X} (e-eq : is-group.e G == is-group.e H)
    (comp-eq : is-group._·_ G == is-group._·_ H) (i-eq : is-group.i G == is-group.i H) where
    private
      module G = is-group G
      module H = is-group H
      open is-group H using (_·_)

    ass-tp : ((x₁ x₂ x₃ : X) → ((x₁ G.· x₂) G.· x₃) == (x₁ G.· (x₂ G.· x₃)))
           → (x₁ x₂ x₃ : X) → ((x₁ · x₂) · x₃) == (x₁ · (x₂ · x₃))
    ass-tp = transport (λ x → (x₁ x₂ x₃ : X) → x (x x₁ x₂) x₃ == x x₁ (x x₂ x₃)) comp-eq

    unit-l-tp : ((x₂ : X) → (G.e G.· x₂) == x₂) → (x₂ : X) → (H.e · x₂) == x₂
    unit-l-tp = transport2 (λ x x₁ → (x₂ : X) → x₁ x x₂ == x₂) e-eq comp-eq

    inv-l-tp : ((x : X) → (G.i x G.· x) == G.e) → (x : X) → (H.i x · x) == H.e
    inv-l-tp = transport3 (λ z z₁ z₂ → (x : X) → z₂ (z x) x == z₁) i-eq e-eq
      comp-eq

    all-paths : ∀ {x y : X} → (p q : x == y) → (p == q)
    all-paths {x} {y} = λ p q → H.set x y p q

      {- We need to specify the following types: -}
    set-path : G.set == H.set
    set-path = is-hset-is-hprop G.set H.set

    ass-path : ass-tp G.ass == H.ass
    ass-path = hprop-dep-prod3 (λ x y z → all-paths)
                             (ass-tp G.ass)
                             H.ass

    unit-l-path : unit-l-tp G.unit-l == H.unit-l
    unit-l-path = hprop-dep-prod (λ x → all-paths)
                                (unit-l-tp G.unit-l)
                                H.unit-l

    inv-l-path : inv-l-tp G.inv-l == H.inv-l
    inv-l-path = hprop-dep-prod (λ x → all-paths) (inv-l-tp G.inv-l) H.inv-l


  record is-group-eq  (G H : is-group X) : Set α where
    constructor is-group-eq-in
    private
      module G = is-group G
      module H = is-group H
      open is-group H using (_·_)

    field
      e-eq : G.e == H.e
      comp-eq :  G._·_ == H._·_
      i-eq :  G.i == H.i

    open is-group-eq-transports {G} {H} e-eq comp-eq i-eq

    {- The following paths can probably be deduced from the above and the fact
       we are dealing with hsets. -}
    field
      set-eq : G.set == H.set
      ass-eq : ass-tp G.ass == H.ass
      unit-l-eq : unit-l-tp G.unit-l == H.unit-l
      inv-l-eq : inv-l-tp G.inv-l == H.inv-l

  {- This is a more convenient way to create an equivalence. You only need
     three paths instead of seven... -}
  is-group-eqv : {G H : is-group X} → (e-eq : is-group.e G == is-group.e H) →
                   (comp-eq :  is-group._·_ G == is-group._·_ H) →
                   (i-eq : is-group.i G == is-group.i H) →
                   (is-group-eq G H)
  is-group-eqv {G} {H} idp idp idp = lemma
    where
      module G = is-group G
      module H = is-group H
      open is-group-eq-transports {G} {H} idp idp idp

      lemma : is-group-eq G H
      lemma = is-group-eq-in idp idp idp set-path ass-path unit-l-path inv-l-path

  encode : (G H : is-group X) → (G == H) → is-group-eq G H
  encode G .G idp = is-group-eq-in idp idp idp idp idp idp idp

  {- Here we need to somehow use the 3 idps and the deduced paths.. -}
  decode : (G H : is-group X) → (is-group-eq G H) → G == H
  decode record { e = .(is-group.e H) ; _·_ = .(is-group._·_ H)
                ; i = .(is-group.i H) ; ass = .(is-group.ass H)
                ; unit-l = .(is-group.unit-l H) ; inv-l = .(is-group.inv-l H)
                ; set = .(is-group.set H) }
                H (is-group-eq-in idp idp idp idp idp idp idp) = idp

  f-g : (G H : is-group X) → (eqv : is-group-eq G H) → encode G H (decode G H eqv) == eqv
  f-g record { e = .(is-group.e H) ; _·_ = .(is-group._·_ H)
             ; i = .(is-group.i H) ; ass = .(is-group.ass H)
             ; unit-l = .(is-group.unit-l H) ; inv-l = .(is-group.inv-l H)
             ; set = .(is-group.set H) }
             H (is-group-eq-in idp idp idp idp idp idp idp) = idp

  g-f : (G H : is-group X) → (p : G == H) → (decode G H (encode G H p) == p)
  g-f G .G idp = idp

  is-group-eq-qinv : (G H : is-group X) → (qinv (encode G H))
  is-group-eq-qinv G H = record {g = decode G H ; f-g = f-g G H ; g-f = g-f G H}

{- We need univalence to show that the two underlying universes are equal. -}
postulate
  ua : ∀ {i} {A B : Set i} → (A ≃ B) → (A == B)

{- Here we define the idtoiso type. -}
module _ {i} {G H : Group i} (iso : G ≃ᴳ H) where
  private
    module G = Group G
    module H = Group H
    open GroupHom (Σ.fst iso)
    module Genc = is-group-encode-decode
    open Σ-encode-decode

    {- It will be more convenient to handle Σ types instead of Groups. -}
    Σ-Group : Set (lsucc i)
    Σ-Group = Σ (Set i) λ x → is-group x

    Group→Σ : (G : Group i) → Σ-Group
    Group→Σ (group U struct) = U , struct

    Σ→Group : (Gs : Σ-Group) → Group i
    Σ→Group (U , proof) = group U proof

    {- They are the same thing anyway. -}
    Group→Σ→Group==id : {G : Group i} → Σ→Group (Group→Σ G) == G
    Group→Σ→Group==id = idp

    {- If we can create a Σ-eq from the isomorphism we are basically done. -}
    iso→Σ-eq : Σ-eq (Group→Σ G) (Group→Σ H)
    iso→Σ-eq = Σ-eq-in U-path (Genc.decode G→H-tp H.struct
                                (Genc.is-group-eqv e-path comp-path i-path))
      where
        open _≃ᴳ_ iso
        open is-group

        U-path : G.U == H.U
        U-path = ua (f , (Σ.snd iso))

        G→H-tp : is-group H.U
        G→H-tp = transport is-group U-path G.struct

        e-path : e G→H-tp == H.e
        e-path = {!   !}

        comp-path : _·_ G→H-tp == H.comp
        comp-path = {!   !}

        i-path : is-group.i G→H-tp == H.i
        i-path = {!   !}

    {- From the Σ-eq we get the required identity. -}
    iso→Σid : Σ→Group (Group→Σ G) == Σ→Group (Group→Σ H)
    iso→Σid = ap Σ→Group (decode (Group→Σ G) (Group→Σ H) iso→Σ-eq)

  isotoid : G == H
  isotoid =
    begin
      G
    ==⟨ ! Group→Σ→Group==id ⟩
      Σ→Group (Group→Σ G)
    ==⟨ iso→Σid ⟩
      Σ→Group (Group→Σ H)
    ==⟨ Group→Σ→Group==id ⟩
      H
    ∎
