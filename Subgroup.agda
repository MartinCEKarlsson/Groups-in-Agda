{-# OPTIONS --without-K --rewriting #-}
open import Equality
open import PropositionsAsTypes
open import Agda.Primitive renaming (_⊔_ to lmax ; Level to ULevel ; lsuc to lsucc)
open import Equivalences2
open import Eq-reasoning
open import Group

{-- in this file we formalize subgroups and normal subgroups --}

