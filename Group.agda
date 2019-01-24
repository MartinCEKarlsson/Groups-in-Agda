{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences
open import Eq-reasoning
open import SetsAndProps

{- This file draws heavily from the HOTT-library -}

record is-group {ℓ} (X : Set ℓ) : Set ℓ where
  field
    {-
    A group G is an algebra hG; ·; −1; 1i with a binary, a unary, and
    nullary operation in which the following identities are true:
    G1: x · (y · z) ≈ (x · y) · z
    G2: x · 1 ≈ 1 · x ≈ x
    G3: x · x−1 ≈ x−1 · x ≈ 1

    Prove that we can weaken the axioms for a group (G; ∗) as
    follows.
    1. The binary operation is associative.
    2. There exists a left identity e in G such that ex = x for all x 2 G.
    3. For each a 2 G there exists a left inverse a0 2 G such that a0a = e
    -}

    e : X
    _·_ : X → X → X
    i : X → X
    ass : ∀ a b c → ((a · b) · c) == (a · (b · c))
    is-unit : ∀ a → (a · e) == e
    inv₁ : ∀ a → ((i a) · a) == e
    inv₂ : ∀ a → (a · (i a)) == e
    set : is-hset X

  private
    e==e : e == e
    e==e =
      begin
        e
      ==⟨ idp ⟩
        e
      ∎

  abstract
    e==e·e : e == (e · e)
    e==e·e =
      begin
        e
      ==⟨ ! (is-unit e) ⟩
        e · e
      ∎


record Group ℓ : Set (lsucc ℓ) where
  constructor group
  field
    U : Set ℓ
    struct : is-group U
  open is-group struct renaming (_·_ to comp) public

idf : ∀ {i} {X : Set i} → (X → X)
idf X = X

record Subgrp {i j} (G : Group i) : Set (lmax (lsucc j) i) where
  private
    module G = Group G
  field
    prop : G.U → Set j
    f : ∀ {a : G.U} → is-hprop( prop a)
    id : prop G.e
    comp : ∀ {a b : G.U} → prop a → prop b → prop (G.comp a b)

{- Normal subgroups : -}
is-normal : {ℓ : ULevel} {Grp : Group ℓ} → (Subgrp {ℓ} {ℓ} Grp) → Set ℓ
is-normal {ℓ} {Grp} H = (g : U) → (h : U) → prop h → prop (g ×ᴳ (h ×ᴳ (iᴳ g)))
  where
    open Group Grp renaming (comp to _×ᴳ_; i to iᴳ)
    open Subgrp H renaming (comp to _×ᴴ_)

record GroupHom {i j} (G : Group i) (H : Group j) : Set (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
  field
    f : G.U → H.U
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

→ᴳ-id : ∀ {i} {G : Group i} → G →ᴳ G
→ᴳ-id = group-hom (λ x → x) (λ g₁ g₂ → idp)

→ᴳ-trans : ∀ {i j k} {G : Group i} {H : Group j} {J : Group k} → G →ᴳ H → H →ᴳ J → G →ᴳ J
→ᴳ-trans (group-hom g p) (group-hom h q) =
  group-hom (λ z → h (g z)) (λ a b → transitive (ap h (p a b)) (q (g a) (g b)))

_≃ᴳ_ : ∀ {i j} (G : Group i) (H : Group j) → Set (lmax i j)
G ≃ᴳ H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))
infix 100 _≃ᴳ_
module _≃ᴳ_ {i j} {G : Group i} {H : Group j} (iso : G ≃ᴳ H) where

  open Group H renaming (comp to _×ᴴ_)
  open Group G renaming (comp to _×ᴳ_)
  open GroupHom (Σ.fst iso)
  open is-hae (is-equiv→is-hae f (Σ.snd iso))

  preserves-comp : (a' b' : Group.U H) → g (Group.comp H a' b') == Group.comp G (g a') (g b')
  preserves-comp a' b' =
    begin
      g (a' ×ᴴ b')
    ==⟨ ap g (ap2 (! (f-g a')) (! (f-g b')) {_×ᴴ_}) ⟩
      g ((f (g a')) ×ᴴ (f (g b')))
    ==⟨ ap g (! (pres-comp (g a') (g b'))) ⟩
      g (f ((g a') ×ᴳ (g b')))
    ==⟨ g-f (((g a') ×ᴳ (g b'))) ⟩
      (g a') ×ᴳ (g b')
    ∎

  g-hom : H →ᴳ G
  g-hom = group-hom g preserves-comp

  f-hom : G →ᴳ H
  f-hom = Σ.fst iso

  adj' : (a' : Group.U H) → ap g (f-g a') == g-f (g a')
  adj' a' = is-group.set
    (Group.struct G)
    (g (f (g a')))
    (g a')
    (ap g (f-g a'))
    (g-f (g a'))

  sym : (H ≃ᴳ G)
  sym = g-hom , is-hae→is-equiv g (record { g = f
                                          ; f-g = g-f
                                          ; g-f = f-g
                                          ; adj = adj' })

–>ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (iso : G ≃ᴳ H) → (G →ᴳ H)
–>ᴳ = _≃ᴳ_.f-hom

<–ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (G ≃ᴳ H) → (H →ᴳ G)
<–ᴳ = _≃ᴳ_.g-hom

sym : ∀ {i j} (G : Group i) (H : Group j) → (G ≃ᴳ H) → (H ≃ᴳ G)
sym G H = _≃ᴳ_.sym

{- We want some sort of convenient equivalence for is-group records. -}
module is-group-encode-decode {α : ULevel} {X : Set α} where
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

    private
      ass-tp : ((x₁ x₂ x₃ : X) → ((x₁ G.· x₂) G.· x₃) == (x₁ G.· (x₂ G.· x₃)))
             → (x₁ x₂ x₃ : X) → ((x₁ · x₂) · x₃) == (x₁ · (x₂ · x₃))
      ass-tp = transport (λ x → (x₁ x₂ x₃ : X) → x (x x₁ x₂) x₃ == x x₁ (x x₂ x₃)) comp-eq

      is-unit-tp : ((x : X) → (x G.· G.e) == G.e) → (x : X) → (x · H.e) == H.e
      is-unit-tp = transport2 (λ z z₁ → (x : X) → z₁ x z == z) e-eq comp-eq

      inv₁-tp : ((x : X) → (G.i x G.· x) == G.e) → (x : X) → (H.i x · x) == H.e
      inv₁-tp = transport3 (λ z z₁ z₂ → (x : X) → z₂ (z x) x == z₁) i-eq e-eq
        comp-eq

      inv₂-tp : ((x : X) → (x G.· G.i x) == G.e) → (x : X) → (x · H.i x) == H.e
      inv₂-tp = transport3 (λ z z₁ z₂ → (x : X) → z₂ x (z x) == z₁) i-eq e-eq
          comp-eq

      all-paths : ∀ {x y : X} → (p q : x == y) → (p == q)
      all-paths {x} {y} = λ p q → H.set x y p q

    {- The following paths can probably be deduced from the above and the fact
       we are dealing with hsets. -}
    abstract
      {- We need to specify the following types: -}
      set-eq : G.set == H.set
      set-eq = is-hset-is-hprop G.set H.set

      ass-eq : ass-tp G.ass == H.ass
      ass-eq = hprop-dep-prod3 (λ x y z → all-paths)
                               (ass-tp G.ass)
                               H.ass

      {- The following need some sort of nested transport.. -}
      is-unit-eq : is-unit-tp G.is-unit == H.is-unit
      is-unit-eq = hprop-dep-prod (λ x → all-paths)
                                  (is-unit-tp G.is-unit)
                                  H.is-unit

      inv₁-eq : inv₁-tp G.inv₁ == H.inv₁
      inv₁-eq = hprop-dep-prod (λ x → all-paths) (inv₁-tp G.inv₁) H.inv₁

      inv₂-eq : inv₂-tp G.inv₂ == H.inv₂
      inv₂-eq = hprop-dep-prod (λ x → all-paths) (inv₂-tp G.inv₂) H.inv₂

  encode : (G H : is-group X) → (G == H) → is-group-eq G H
  encode G .G idp = is-group-eq-in idp idp idp

  {- Here we need to somehow use the 3 idps and the deduced paths.. -}
  decode : (G H : is-group X) → (is-group-eq G H) → G == H
  decode G H (is-group-eq-in idp idp idp) = {!   !}

  f-g : (G H : is-group X) → (eqv : is-group-eq G H) → encode G H (decode G H eqv) == eqv
  f-g G H (is-group-eq-in idp idp idp) = {!   !}

  g-f : (G H : is-group X) → (p : G == H) → (decode G H (encode G H p) == p)
  g-f G H idp = idp

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
                                (Genc.is-group-eq-in e-path comp-path i-path))
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

{- We prove the following lemma: every homomorphism maps the identity to the identity -}
id-to-id : {i : ULevel} {G H : Group i} → (f : G →ᴳ H) → (GroupHom.f f (Group.e G) == Group.e H)
id-to-id {i} {G} {H} (group-hom f pres-comp) =
    begin
      f G.e
    ==⟨ {!   !} ⟩
      H.e
    ∎
  where
    module G = Group G
    module H = Group H

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : ∀ {i} {G H : Group i} → (G == H) → (G ≃ᴳ H)
idtoiso {i} {G} {.G} idp = →ᴳ-id , (λ y → build-is-contr (y , idp) (λ {(x , idp) → idp}))

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {i : ULevel} {G H : Group i} (p : G == H) → (Subgrp {i} {i} G) → (Subgrp {i} {i} H)
idtoiso-subgrp {i} {G} {H} p G' = record { prop = λ x → Subgrp.prop G' (θ-inv(x)) ; f = Subgrp.f G' ; id = {!  !}  ; comp = {!  !} }
  where
    open Group H renaming (comp to _×ᴴ_)
    open Group G renaming (comp to _×ᴳ_)

    equiv : (G ≃ᴳ H) -- The equivalence
    equiv = idtoiso p

    open GroupHom (Σ.fst equiv)

    θ : (Group.U G → Group.U H)   -- The forward map of the equivalence
    θ = GroupHom.f (Σ.fst equiv)

    open is-hae (is-equiv→is-hae θ (Σ.snd equiv))

    θ-inv : (Group.U H → Group.U G)  -- The backward map of the equivalence
    θ-inv = g

{- We want to prove that the previous two functions Subgrp G → Subgrp H are homotopic -}
trans-equiv-idtoiso : {i : ULevel} (G H : Group i) → transp-subgrp {i} {G} {H} == idtoiso-subgrp {i} {G} {H}
trans-equiv-idtoiso = {!  !}


{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : {ℓ : ULevel} {G : Group ℓ} (f : (G : Group ℓ) → (Subgrp {ℓ} {ℓ} G)) → (H : Group ℓ) → (is-normal (f H))
def-subgroups-are-normal f H = {!  !}
