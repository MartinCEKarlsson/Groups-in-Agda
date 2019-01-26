{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
{- The first library module we import is lib.Base (Base.agda). This contains all the
   basic definitions such as equality type, Σ types, etc. It also contains the equational
   reasoning notation.
-}

{- lib.Base defines the function coe : {A B : Type ℓ} → A == B → A → B by path induction.
   coe is taken to be fundamental and
   many other basic functions are defined in terms of it, including for instance
   transport and univalence.

   An important notational point is that heterogeneous equality has its own special notation.
   Suppose we are given a type X and Y : X → Type, together with a path p : x == x' in X.
   If we are given y : Y x and y' : Y x', we use the notation y == y' [ Y ↓ p ] for
   "heterogeneous equality over p" or "paths over p". We can think of this as
   the same as (transport Y p y) == y', although in the library y == y' [ Y ↓ p ] is defined
   directly via path induction, and later proved to be equivalent to (transport Y p y) == y'.
-}

open import lib.PathGroupoid
{- PathGroupoid contains basic manipulations of paths and homotopies, such as concatenation ∙
   whiskering ∙ₗ and ∙ᵣ inverse paths ! and various related functions. -}

open import lib.Equivalence
{- lib.Equivalence contains functions for defining and working with equivalences.
   We write the type of equivalences from X to Y as X ≃ Y. We can extract the underlying
   function using –> (\en>). We can also extract the inverse function using <– (<\en).

   The identity equivalence is ide and equivalences can be composed using ∘e or using
   equational reasoning for equivalences.
-}

open import lib.Funext
{- lib.Funext contains the function extensionality axiom. We end up with an
   equivalence λ=-equiv f ∼ g ≃ f == g. In particular, the underlying
   function of the equivalence is λ= from f ∼ g to f == g.
-}

open import lib.Univalence
{- This contains the univalence axiom. Like many things in the library the definition of
   univalence is based on coe. To define univalence they first define a function coe-equiv
   from A == B to A ≃ B. They then assert the existence of an equivalence
   ua-equiv : (A ≃ B) ≃ (A == B) whose inverse component is coe-equiv. The underlying
   function of ua-equiv is written ua.
-}

{- The modules in lib.types contain functions about specific types. Usually this includes
   some version of the encode-decode method and some functions for generating equivalences
   between different types. -}
open import lib.types.Pi
open import lib.types.Sigma

module Magma {ℓ : ULevel} where

{- A magma is a type with a binary operation.
   We are going to characterise the equality type on Magmas.
-}
record Magma : Type (lsucc ℓ) where -- the type of all Magmas at level ℓ itself has level (lsucc ℓ)
  field
    X : Type ℓ -- the carrier type
    _∗_ : X → X → X -- the binary operation

{- To fully exploit the HoTT-Agda library we mostly work with an equivalent definition
   given as a Σ type.
-}
Magma' : Type (lsucc ℓ)
Magma' = Σ (Type ℓ) (λ X → (X → X → X))

{- To show the types are equivalent, we use the function equiv, which takes the components
   of a quasi equivalence as input and returns an equivalence.
-}
magma-equiv : Magma ≃ Magma'
magma-equiv = equiv f g f-g g-f
  where
    f : Magma → Magma'
    f record { X = X ; _∗_ = _∗_ } = X , _∗_

    g : Magma' → Magma
    g (fst , snd) = record { X = fst ; _∗_ = snd }

    f-g : (M : Magma') → (f (g M) == M)
    f-g (fst₁ , snd₁) = idp

    g-f : (M : Magma) → (g (f M) == M)
    g-f M = idp



{- A demonstration of equational reasoning for equivalences. Note that this is very
   similar to equational reasoning.
-}
λ=-equiv2 : {α : ULevel} {A B C : Type α} (f g : A → B → C) →
            ((a : A) → (b : B) → (f a b == g a b)) ≃
              (f == g)
λ=-equiv2 {α} {A} {B} f g =
  ((a : A) → (b : B) → (f a b == g a b)) -- definitionally equal to (a : A) → (f a ∼ g a)
    ≃⟨ Π-emap-r (λ a → λ=-equiv) ⟩
  {- We need to show that two dependent products are equivalent. We know already that they
     have exactly the same domain, and for each element of that domain, the corresponding
     types are equivalent. For this we use the function Π-emap-r.

     λ=-equiv is the equivalence given by function extensionality.
  -}
  ((a : A) → (f a == g a)) -- definitionally equal to f ∼ g
    ≃⟨ λ=-equiv ⟩
  f == g
    ≃∎

{- As a corollary we get the following lemma. Note here that we are using the notation
   f == g [ (λ X → (X → X → X)) ↓ p ] for paths over p/heterogeneous equality.
-}
fun-paths-equiv : {α : ULevel} (B B' : Type α) (p : B == B') →
        (f : B → B → B) (g : B' → B' → B') →
        ((b b' : B) → coe p (f b b') == g (coe p b) (coe p b')) ≃
        (f == g [ (λ X → (X → X → X)) ↓ p ])
fun-paths-equiv B .B idp f g = λ=-equiv2 f g

{- An explicit description of what the equality type on Magma' ought to be. -}
magma'= : (M N : Magma') → (Type ℓ)
magma'= M N = Σ ((fst M) ≃ (fst N))
               (λ e → (m m' : fst M) → (–> e (snd M m m') == (snd N (–> e m) (–> e m'))))

{- We prove that magma'= is indeed equivalent to M == N. -}
magma'=-equiv : (M N : Magma') → ((magma'= M N) ≃ (M == N))
magma'=-equiv M N =
  Σ ((fst M) ≃ (fst N))
               (λ e → (m m' : fst M) → (–> e (snd M m m') == (snd N (–> e m) (–> e m'))))
    ≃⟨ Σ-emap-r (λ e → coe-equiv (ap (λ f → ((m m' : fst M) → f (snd M m m') == snd N (f m) (f m')))
                                        (λ= λ a → ! (coe-β e a)))) ⟩
  {- The first step is the most complicated, so let's break it down. The first two lines
     differ only in the second component of the Σ type, so using Σ-emap-r we just have to
     show the second components are equivalent. In fact we can prove more than this - we will
     show the second components are equal, so we use coe-equiv to convert the equality to
     an equivalence. To prove equality, we notice that the functions (–> e) and (coe (–> ua-equiv e))
     are homotopic using coe-β from Equivalence.agda, so by function extensionality (λ=) they are
     equal as functions, and so we can substitute using ap.
  -}
  (Σ (fst M ≃ fst N) (λ e → (m m' : (fst M)) → coe (–> ua-equiv e) (snd M m m') ==
                                                  (snd N (coe (–> ua-equiv e) m) (coe (–> ua-equiv e) m'))))
    ≃⟨ Σ-emap-l _ ua-equiv ⟩
  {- This time we use the fact that the first components of the Σ types are equivalent (via
     univalence), together with the function Σ-emap-l from lib.types.Sigma
  -}
  (Σ (fst M == fst N) (λ p → (m m' : (fst M)) → coe p (snd M m m') == (snd N (coe p m) (coe p m'))))
    ≃⟨ Σ-emap-r (λ p → fun-paths-equiv (fst M) (fst N) p (snd M) (snd N)) ⟩
  {- Again we use equivalence of the second component of the Σ types and Σ-emap-r, via the
     lemma fun-paths-equiv we proved earlier. -}
  (Σ (fst M == fst N) (λ p → (snd M) == (snd N) [ (λ X → (X → X → X)) ↓ p ]))
    ≃⟨ =Σ-econv M N ⟩
  (M == N)
    ≃∎

record magma= (M N : Magma) : Type ℓ where
  open Magma
  field
    carrier-equiv : X M ≃ X N
    preserves-operator : (m m' : X M) → (–> carrier-equiv (_∗_ M m m') ==
                                            _∗_ N (–> carrier-equiv m) (–> carrier-equiv m'))

{- Finally, if necessary we can package up everything in record type again. -}
magma=-equiv-equiv : (M N : Magma) → (magma= M N ≃ magma'= (–> magma-equiv M) (–> magma-equiv N))
magma=-equiv-equiv M N = equiv f g f-g g-f
  where
    f : magma= M N → magma'= (–> magma-equiv M) (–> magma-equiv N)
    f eq = (magma=.carrier-equiv eq) , (magma=.preserves-operator eq)

    g : magma'= (–> magma-equiv M) (–> magma-equiv N) → magma= M N
    g (fst₁ , snd₁) = record {carrier-equiv = fst₁ ; preserves-operator = snd₁}

    f-g : (p : magma'= (–> magma-equiv M) (–> magma-equiv N)) → (f (g p) == p)
    f-g x = idp

    g-f : (p : magma= M N) → (g (f p) == p)
    g-f p = idp

magma=-equiv : (M N : Magma) → ((magma= M N) ≃ (M == N))
magma=-equiv M N =
  magma= M N
    ≃⟨ magma=-equiv-equiv M N ⟩
  magma'= (–> magma-equiv M) (–> magma-equiv N)
    ≃⟨ magma'=-equiv (–> magma-equiv M) (–> magma-equiv N) ⟩
  (–> magma-equiv M) == (–> magma-equiv N)
    ≃⟨ (ap-equiv magma-equiv M N)⁻¹ ⟩
    {- Given an equivalence, ap induces an equivalence on each identity type via ap-equiv
       (which appears in lib.Equivalence).
    -}
  M == N
    ≃∎
