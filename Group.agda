{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences2
open import Eq-reasoning


{-
This file draws heavily from the HOTT-library
-}

{- A type is an h-proposition or mere proposition if we can (uniformly) construct a path
   between any two points.
-}
is-hprop : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hprop X = (x y : X) → (x == y)

{- A type is an h-set if every identity type is an h-proposition. -}
is-hset : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hset X = (x y : X) → is-hprop (x == y)

{-
hGroup : Set
hGroup = Σ Set (λ Y → is-hset Y)

record GroupStructure {i} (El : Set i) --(El-level : has-level 0 El)
  : Set i where
  constructor group-structure
  field
    ident  : El
    inv    : El → El
    comp   : El → El → El
    unit-l : ∀ a → comp ident a == a
    assoc  : ∀ a b c → comp (comp a b) c == comp a (comp b c)
    inv-l  : ∀ a → (comp (inv a) a) == ident
-}

--record is-group {ℓ} (X : Set ℓ) (e : X) (_·_ : X → X → X) (i : X → X) : Set ℓ where
record is-group {ℓ} (X : Set ℓ) (e : X) (_·_ : X → X → X) (i : X → X) : Set ℓ where
  field
    ass : ∀ a b c → ((a · b) · c) == (a · (b · c))
    is-unit : ∀ a → (a · e) == e
    inv₁ : ∀ a → ((i a) · a) == e
    inv₂ : ∀ a → (a · (i a)) == e
    proof : is-hset X

  asdf : ∀ a → (a · e) == e → e == (a · e)
  asdf = λ a x → symmetric (a · e) e x


  e==e : e == e
  e==e =
    begin
      e
    ==⟨ idp ⟩
      e
    ∎


  asdf2 : (e · e) == e → e == (e · e)
  asdf2 = symmetric (e · e) e

  asdf3 : e == (e · e)
  asdf3 = asdf2 (is-unit e)
  abstract
    e==e·e : e == (e · e)
    e==e·e =
      begin
        e
      ==⟨ asdf2 (is-unit e) ⟩
        e · e
      ∎

open is-group

record Group ℓ : Set (lsucc ℓ) where
  constructor group
--record Group c ℓ : Set where
--record Group c ℓ : Set (suc (c ⊹ ℓ)) where
  --infix  8 _⁻¹
  --infixl 7 _∙_
  --infix  4 _≈_
  field
    U : Set ℓ
    e : U
    comp : U → U → U
    i : U → U
    proof : is-group U e comp i

idf :  (X : Set ) → X → X
idf X x = x

{-
preserves-comp : ∀ {i j} {A : Set i} {B : Set j}
  (A-comp : A → A → A) (B-comp : B → B → B) (f : A → B)
  → Set (lmax i j)
preserves-comp Ac Bc f = ∀ a₁ a₂ → f (Ac a₁ a₂) == Bc (f a₁) (f a₂)
-}

record GroupHom {i j} (G : Group i) (H : Group j) : Set (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
  field
    f : G.U → H.U
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)
  --open GroupStructureHom {GS = G.group-struct} {HS = H.group-struct}
  --  record {f = f ; pres-comp = pres-comp} hiding (f ; pres-comp) public
infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

_≃ᴳ_ : ∀ {i j} (G : Group i) (H : Group j) → Set (lmax i j)
G ≃ᴳ H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))
infix 100 _≃ᴳ_
module _≃ᴳ_ {i j} {G : Group i} {H : Group j} (iso : G ≃ᴳ H) where
  --constructor c

  f-hom : G →ᴳ H
  f-hom = Σ.fst iso

  g-hom : H →ᴳ G
  g-hom = group-hom (is-hae.g (is-equiv→is-hae (GroupHom.f (f-hom)) (Σ.snd iso))) {!   !}
-- lemma : ∀ {i j} (G : Group i) (H : Group j) → (G ≃ᴳ H) → (H →ᴳ G)
-- lemma G H x = group-hom (λ x₁ → Group.e G) (λ g₁ g₂ → e==e·e {! G  !})

–>ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (iso : G ≃ᴳ H) → (G →ᴳ H)
–>ᴳ = _≃ᴳ_.f-hom

<–ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (G ≃ᴳ H) → (H →ᴳ G)
<–ᴳ = _≃ᴳ_.g-hom

sym : ∀ {i j} (G : Group i) (H : Group j) → (G ≃ᴳ H) → (H ≃ᴳ G)
sym G H x = {!   !} , {!   !}


postulate
  pro : {x y : ⊤} {p q : x == y} → p == q


⊤-is-group : is-group ⊤ unit (λ x y → unit) (λ x → unit)
⊤-is-group = record { ass = λ a b c → idp ; is-unit = λ a → idp ; inv₁ = λ a → idp ; inv₂ = λ a → idp ; proof = λ x y x₁ y₁ → pro }
