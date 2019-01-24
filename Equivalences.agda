{-# OPTIONS --without-K #-}

open import PropositionsAsTypes
open import Equality

{- When we import a module we can use the renaming keyword to change
   some of the names, for example if we want to use the name for
   something else. In this case we are going to follow the same
   naming convention as the HoTT-Agda library. We relabel Level to
   ULevel and _⊔_ to lmax.
-}
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)

module Equivalences where

{- Nearly all of the types we have seen so far have been elements of the
   universe type, Set. For example, using C-c C-d you can see that Bool
   has type Set.

   However, there is a big exception to this. Set itself is not of type
   Set. If you try this with C-c C-d you will see that the type of Set
   is Set₁. The reason for this is that if we take Set to be an element of
   itself we can end up with paradoxes. To solve this, we add another universe
   Set₁ which contains Set, so we can work with Set similarly to any other
   type. We then have the same problem with Set₁. Using C-c C-d you can see
   that the type of Set₁ is another universe, Set₂.

   More generally, we have a type ULevel of universe levels, and for each
   universe level α, a universe Set α.
-}

{- This is a universe polymorphic version of Σ types. We take two universe
   levels as implicit parameters, α and β. We think of lmax as the maximum
   of α and β, so that given types from Set α and Set β we can construct
   types in Set (lmax α β).
-}
--postulate
--  ℓ : ULevel

{- Recall the definition of is-contr (is contractible) from last time. -}
record is-contr {α : ULevel} (X : Set α) : Set α where
  constructor build-is-contr
  field
    center : X
    path : (x : X) → (x == center)


record qinv {α β : ULevel} {X : Set α} {Y : Set β} (f : X → Y) : Set (lmax α β) where
  field
    g : Y → X
    f-g : (y : Y) → (f (g y) == y)
    g-f : (x : X) → (g (f x) == x)


{- We say two functions f and g are homotopic (f ∼ g) if f a == g a for all a -}
_∼_ : {α β : ULevel} {A : Set α} {B : A → Set β} (f g : (a : A) → B a) → Set (lmax α β)
_∼_ {α} {β} {A} f g = (a : A) → f a == g a

{- You might find it useful later to use these earlier exercises. -}
homotopy-commutes : {α β : ULevel} {A : Set α} {B : Set β} (f g : A → B)
                    (H : f ∼ g) (x y : A) (p : x == y) →
                    (H x ∙ (ap g p) == (ap f p) ∙ H y)
homotopy-commutes f g H x .x idp =  ! (∙-unit-l (H x))

whisker-l : {ℓ : ULevel } {X : Set ℓ} {x y z : X} (p q : x == y) (α : p == q) (r : y == z) →
            (p ∙ r == q ∙ r)
whisker-l p .p idp r = idp

whisker-r : {ℓ : ULevel} {X : Set ℓ} {x y z : X} (p : x == y) (q r : y == z) (α : q == r) →
            (p ∙ q == p ∙ r)
whisker-r p q .q idp = idp

{- We will also use the encode-decode method for Σ types. -}

record Σ {α β : ULevel} (A : Set α) (B : A → Set β) : Set (lmax α β) where
  constructor _,_
  field
    fst : A
    snd : B fst

module Σ-encode-decode {α β : ULevel} {A : Set α} {B : A → Set β} where

  {- The first step is to define a relation on Σ A B that should be equivalent
     to the identity type. For this we will use the record type Σ-eq below.
  -}
  record Σ-eq (ab ab' : Σ A B) : Set (lmax α β) where
    constructor Σ-eq-in
    field
      fst-eq : Σ.fst ab == Σ.fst ab'
      snd-eq : (transport {α} {β} {A} B fst-eq (Σ.snd ab)) == Σ.snd ab'
        {- note that Σ.snd ab == Σ.snd ab' would not be a well defined type
          since Σ.snd ab and Σ.snd ab' have different types -}

  {- The encode function maps from the real equality type into the new relation. -}
  encode : (ab ab' : Σ A B) → (ab == ab') → Σ-eq ab ab'
  encode ab .ab idp = Σ-eq-in idp idp


  {- We aim to find a quasi inverse for encode ab ab' for each ab and ab'. -}

  {- The underlying function g will be the function decode below. -}
  decode : (ab ab' : Σ A B) → (Σ-eq ab ab') → ab == ab'
  decode (fst , snd) (.fst , .snd) (Σ-eq-in idp idp) = idp

  {- We now need to check that this does give a quasi inverse. -}
  f-g : (ab ab' : Σ A B) → (x : Σ-eq ab ab') → encode ab ab' (decode ab ab' x) == x
  f-g (fst , snd) (.fst , .snd) (Σ-eq-in idp idp) = idp

  g-f : (ab ab' : Σ A B) → (p : ab == ab') → (decode ab ab' (encode ab ab' p) == p)
  g-f (fst , snd) (.fst , .snd) idp = idp

  {- Finally we package everything together to get an element of qinv (encode ab ab')
     for each ab and ab'.
  -}
  Σ-eq-qinv : (ab ab' : Σ A B) → (qinv (encode ab ab'))
  Σ-eq-qinv ab ab' = record {g = decode ab ab' ; f-g = f-g ab ab' ; g-f = g-f ab ab'}



{- Fix a function f : X → Y -}
module _ {α β : ULevel} {X : Set α} {Y : Set β} (f : X → Y) where

  {- We have already seen two definitions of what it means for f to have an equivalence. -}

  {- The next was that f has contractible fibers. -}
  hfiber : (y : Y) → Set (lmax α β)
  hfiber y = Σ X (λ x → f x == y)

  {- When working with hfibers, it is useful to use the following more explicit
     description of when two hfibers are equal. It is sufficient to first construct a
     path between
  -}
  hfiber-dec : (y : Y) (xp xp' : hfiber y) (p : Σ.fst xp == Σ.fst xp')
               (r : (ap f p) ∙ (Σ.snd xp') == Σ.snd xp) → (xp == xp')
  hfiber-dec y (.(Σ.fst xp') , .(idp ∙ Σ.snd xp')) xp' idp idp =
    Σ-encode-decode.decode _ _ (Σ-encode-decode.Σ-eq-in idp (∙-unit-l _))

  hfiber-enc : (y : Y) (xp xp' : hfiber y) (p : xp == xp') →
               (Σ (Σ.fst xp == Σ.fst xp') (λ q → (ap f q) ∙ (Σ.snd xp') == Σ.snd xp))
  hfiber-enc y xp .xp idp = idp , ∙-unit-l _

  is-equiv = (y : Y) → is-contr (hfiber y)

  {- We saw that equiv has the advantage that it is always an h-proposition, so it
     is "property rather than structure."
  -}

  {- We will now see two more definitions of equivalence, each useful in certain
     situations. To say f is a Joyal equivalence is to find a term of the type
     jequiv below.
  -}
  record is-jequiv : Set (lmax α β) where
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      h : Y → X
      h-f : (x : X) → (h (f x) == x)



  {- Trivially, every quasi inverse can be seen as a proof that f is a Joyal equivalence. -}
  qinv-to-jequiv : qinv f → is-jequiv
  qinv-to-jequiv inv = record { g = qinv.g inv
                              ; f-g = qinv.f-g inv
                              ; h = qinv.g inv
                              ; h-f = qinv.g-f inv }

  {- Exercise 1: Show that if a function is a Joyal equivalence, then it has a quasi inverse. -}
  record is-hae : Set (lmax α β) where
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      g-f : (x : X) → (g (f x) == x)
      adj : (x : X) → ap f (g-f x) == f-g (f x)


  postulate
    is-hae→is-equiv : is-hae → is-equiv
    is-equiv→is-hae : is-equiv → is-hae

_≃_ : ∀ {α β} → (A : Set α) → (B : Set β) → Set (lmax α β)
X ≃ Y = Σ (X → Y) is-equiv
