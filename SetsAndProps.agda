{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences

module SetsAndProps where

postulate
  funext : {ℓ ℓ' : ULevel} {X : Set ℓ} {Y : X → Set ℓ'} (f g : (x : X) → Y x) → (f ∼ g) → (f == g)

{- A type is an h-proposition or mere proposition if we can (uniformly) construct a path
   between any two points.
-}
is-hprop : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hprop X = (x y : X) → (x == y)

{- A type is an h-set if every identity type is an h-proposition. -}
is-hset : {ℓ : ULevel} (X : Set ℓ) → Set ℓ
is-hset X = (x y : X) → is-hprop (x == y)

hprop-lemma : {ℓ : ULevel} {X : Set ℓ} (f : is-hprop X) (x y : X) (p : x == y) → (f x y == p)
hprop-lemma {ℓ} {X} f x y p = lemma2 ∙ !-cancel-l (f x y) p
  where
    lemma1 : (z : X) (q : y == z) → (f x z == f x y ∙ q)
    lemma1 z idp = idp

    lemma2 : (f x y == f x y ∙ (! (f x y) ∙ p))
    lemma2 = lemma1 y (! (f x y) ∙ p)

    !-cancel-l : (p q : x == y) → (p ∙ ((! p) ∙ q) == q)
    !-cancel-l p idp = !-inv-r p

{- Note that the above lemma tells us that every hprop is an hset. -}
all-hprops-are-hsets : {ℓ : ULevel} {X : Set ℓ} → (is-hprop X) → (is-hset X)
all-hprops-are-hsets f = λ x y → λ p q → ! (hprop-lemma f x y p) ∙ hprop-lemma f x y q

hprop-dep-prod : {ℓ ℓ' : ULevel} {X : Set ℓ} {Y : X → Set ℓ'} (ihp : (x : X) → is-hprop (Y x)) →
                 is-hprop ((x : X) → Y x)
hprop-dep-prod ihp f g = funext f g (λ x → ihp x (f x) (g x))

hprop-dep-prod2 : {i j k : ULevel} {X : Set i} {Y : Set j} {Z : X → Y → Set k}
                  (ihp : (x : X) → (y : Y) → is-hprop (Z x y)) →
                  is-hprop ((x : X) → (y : Y) → Z x y)
hprop-dep-prod2 ihp f g = hprop-dep-prod (λ x h → hprop-dep-prod (ihp x) h) f g

hprop-dep-prod3 : {i j k l : ULevel} {X : Set i} {Y : Set j} {Z : Set k}
                  {F : X → Y → Z → Set l}
                  (ihp : (x : X) → (y : Y) → (z : Z) → is-hprop (F x y z)) →
                  is-hprop ((x : X) → (y : Y) → (z : Z) → F x y z)
hprop-dep-prod3 ihp f g = hprop-dep-prod2 (λ x y f' g' → hprop-dep-prod (ihp x y) f' g') f g

hprop-is-hprop : {ℓ : ULevel} {X : Set ℓ} → (is-hprop (is-hprop X))
hprop-is-hprop f g = funext f g λ a → hprop-dep-prod (λ x p q → ! (hprop-lemma f a x p) ∙ hprop-lemma f a x q) (f a) (g a)

is-hset-is-hprop : {ℓ : ULevel} {X : Set ℓ} → (is-hprop (is-hset X))
is-hset-is-hprop isSet isSet2 = funext (isSet) (isSet2) (λ x → hprop-dep-prod (λ y isProp isProp2 → hprop-is-hprop isProp isProp2) (isSet x) (isSet2 x))
