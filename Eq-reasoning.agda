open import lib.Base
open import Agda.Primitive renaming (Level to ULevel)
module Eq-reasoning where

  infix  1 begin_
  infixr 2 _==⟨⟩_ _==⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {i} {A : Set i} {x y : A}
    → x == y
      -----
    → x == y
  begin x==y  =  x==y

  _==⟨⟩_ : ∀ {i} {A : Set i} (x : A) {y : A}
    → x == y
      -----
    → x == y
  x ==⟨⟩ x==y  =  x==y

  _==⟨_⟩_ : ∀ {i} {A : Set i} (x : A) {y z : A}
    → x == y
    → y == z
      -----
    → x == z
  x ==⟨ x==y ⟩ y==z = x==y ∙ y==z

  _∎ : ∀ {i} {A : Set i} (x : A)
      -----
    → x == x
  x ∎  =  idp

--open Eq-reasoning
