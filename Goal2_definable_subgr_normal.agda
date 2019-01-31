{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.Univalence
open import lib.Funext
open import lib.NType
open import lib.NType2
open import lib.Funext
open import lib.types.Pi
open import lib.PathGroupoid
open import Magma-basics
open import Group-basics
open import Goal1_isom_groups_are_equal

{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal {α : ULevel} where


module _ where

  idtoiso' : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
  idtoiso' {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)

  paths-are-props : {ℓ : ULevel} {X : Set ℓ} {a b : X} → (isSet : is-set X) → is-prop (a == b)
  paths-are-props {ℓ} {X} {a} {b} isSet = has-level-apply isSet a b
  module _ {α : ULevel} {G H : Group {α}} where

    {- We give an alternative definition of a group homomorphism -}
    GroupHom' : {α β : ULevel} (G : Group {α}) (H : Group {β}) → Set (lmax α β)
    GroupHom' G H = Σ (Group.U G → Group.U H) (λ f → ((g₁ g₂ : Group.U G) → f (Group.comp G g₁ g₂) == Group.comp H (f g₁) (f g₂)))

    {- We prove that the two definitions are equivalent -}
    GroupHom-equiv-GroupHom' : GroupHom G H ≃ GroupHom' G H
    GroupHom-equiv-GroupHom' = ((λ hom → (GroupHom.f hom) , (GroupHom.pres-comp hom)) , record { g =  (λ hom' → group-hom (fst hom') (snd hom')) ; f-g = λ b → idp ; g-f = λ a → idp ; adj = λ a → idp })

    {- For two homomorphisms of type GroupHom', if their underlying map is equal, than the homomorphisms are equal -}
    map-determ-hom' : {hom1 hom2 : GroupHom' G H} → (fst hom1 == fst hom2) → (hom1 == hom2)
    map-determ-hom' {hom1} {hom2} idp = pair= idp (λ= (λ g₁ → λ= λ g₂ → prop-path (paths-are-props (Group.set H)) (snd hom1 g₁ g₂) (snd hom2 g₁ g₂) ))

    {- Map determines homomorphism for type GroupHom -}
    map-determ-hom : {hom1 hom2 : GroupHom G H} → (GroupHom.f hom1 == GroupHom.f hom2) → (hom1 == hom2)
    map-determ-hom {hom1} {hom2} idp = path
      where
        open is-equiv (Σ.snd GroupHom-equiv-GroupHom')

        f : (GroupHom G H → GroupHom' G H )
        f = Σ.fst GroupHom-equiv-GroupHom'


        path : (hom1 == hom2)
        path =
          hom1 =⟨ ! (g-f hom1) ⟩
          g(f(hom1)) =⟨ ap g (map-determ-hom' idp) ⟩
          g(f(hom2)) =⟨ g-f hom2 ⟩
          hom2 =∎

  iso-equiv2 : {G H : Group {α}} → {iso₁ iso₂ : G ≃ᴳ H} → (p : Σ.fst iso₁ == Σ.fst iso₂) → iso₁ == iso₂
  iso-equiv2 {G} {H} {.(fst iso₂) , snd} {iso₂} idp = pair= idp (prop-path is-equiv-is-prop snd (Σ.snd iso₂))

  iso-equiv : {G H : Group {α}} → {iso₁ iso₂ : G ≃ᴳ H} → (p : GroupHom.f (Σ.fst iso₁) == GroupHom.f (Σ.fst iso₂)) → iso₁ == iso₂
  iso-equiv p = iso-equiv2 (map-determ-hom p)



  idtoiso-equiv : {G H : Group {α}} → idtoiso {α} {G} {H} == idtoiso' {G} {H}
  idtoiso-equiv {G} {H} = λ= (λ a → lemma a)
    where
      lemma : (a : G == H) → idtoiso a == idtoiso' a
      lemma idp = iso-equiv (idtoiso-idp-gives-id-map {α} {G})

  idtoiso-idp-equiv : {G : Group {α}} →  idtoiso idp == idtoiso' idp
  idtoiso-idp-equiv {G} = iso-equiv (idtoiso-idp-gives-id-map {α} {G})


{- In this module, we define a function that given an isomorphism between G and H and a subgroup
   of type G, transforms it into a subgroup of type H -}
module _ {G : Group} {H : Group} where
  lift-hom-over-subgrp : (hom : H →ᴳ G) → (Subgrp G → Subgrp  H)
  lift-hom-over-subgrp hom sub-g = record { prop = prop-lemma  ; f = λ {a} → f-lemma a ; id =  id-lemma ; comp =  λ {a} {b} → comp-lemma a b; inv = λ {a} → inv-lemma a}
    where
      open Subgrp sub-g
      open GroupHom hom renaming (f to h-to-g)

      prop-lemma : Group.U H → Set α
      prop-lemma h = prop (h-to-g h)

      f-lemma :  (a : Group.U H) → is-prop (prop-lemma a)
      f-lemma a = f

      id-lemma : prop-lemma (Group.e H)
      id-lemma = coe (ap prop (! id-to-id)) id

      comp-lemma : (a b : Group.U H) → prop-lemma a → prop-lemma b → prop-lemma (Group.comp H a b)
      comp-lemma a b prop-a prop-b = coe (ap prop (! (pres-comp a b))) (comp prop-a prop-b)

      inv-lemma : (a : Group.U H) → prop (h-to-g a) → prop (h-to-g (Group.i H a))
      inv-lemma a prop-a = coe (ap prop (! (pres-i a))) (inv prop-a)

  lift-iso-over-subgrp : (iso : G ≃ᴳ H) → (Subgrp G → Subgrp  H)
  lift-iso-over-subgrp iso sub-g = lift-hom-over-subgrp hom sub-g
    where
      hom : H →ᴳ G
      hom = _≃ᴳ_.g-hom iso


  iso-id-equiv : {G H : Group {α}} (iso : G ≃ᴳ H) → (idtoiso (isotoid iso)) == iso
  iso-id-equiv {G} {H} iso = is-equiv.g-f (snd (iso≃id {α} {G} {H})) iso 

funqeq : {β : ULevel} {A B : Set β} {f g : A → B} (p : f == g) (a : A) → (f a == g a)
funqeq idp a = idp

module _ where

  private
    {- First, we give an alternative definition of a subgroup -}
    record is-subgrp {G : Group {α}} (prop : (Group.U G) → Set α) : Set (lsucc α) where
      private
        module G = Group G
      field
        f : ∀ (a : G.U) → is-prop( prop a)
        id : prop G.e
        comp : ∀ (a b : G.U) → prop a → prop b → prop (G.comp a b)
        inv : ∀ (a : G.U) → prop a → prop (G.i a)

    subgrp' : {G : Group {α}} → Set (lsucc α)
    subgrp' {G} = Σ (Group.U G → Set α) (λ y → is-subgrp {G} y)

    is-prop-is-prop : {ℓ : ULevel} {X : Set ℓ} → (is-prop (is-prop X))
    is-prop-is-prop = has-level-is-prop

    any-isg-with-same-prop-are-equal : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) → (isg1 == isg2)
    any-isg-with-same-prop-are-equal {G} isg1 isg2 = =lemma isg1 isg2 f-eq id-eq comp-eq inv-eq
      where
        open is-subgrp
        f-eq : f isg1 == f isg2
        f-eq = λ= (λ a → prop-path is-prop-is-prop (f isg1 a) (f isg2 a))

        id-eq : id isg1 == id isg2
        id-eq = prop-path (f isg1 (Group.e G)) (id isg1) (id isg2)

        comp-eq : comp isg1 == comp isg2
        comp-eq = λ= (λ a → λ= (λ b → λ= (λ x → λ= λ y → prop-path (f isg1 (Group.comp G a b)) (comp isg1 a b x y) (comp isg2 a b x y))))

        inv-eq : inv isg1 == inv isg2
        inv-eq = λ= (λ a → λ= (λ b → prop-path (f isg1 (Group.i G a)) (inv isg1 a b) (inv isg2 a b)))

        =lemma : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) (eq1 : f isg1 == f isg2) (eq2 : id isg1 == id isg2) (eq3 : comp isg1 == comp isg2) (eq4 : inv isg1 == inv isg2) → (isg1 == isg2)
        =lemma record { f = .(f isg2) ; id = .(id isg2) ; comp = .(comp isg2) ; inv = .(inv isg2) } isg2 idp idp idp idp = idp

    path-prop-implies-path-isg : {G : Group {α}} (pr1 pr2 : (Group.U G) → Set α) (p : pr1 == pr2) (subgr1 : is-subgrp {G} pr1) (subgr2 : is-subgrp {G} pr2) → (transport is-subgrp p subgr1 == subgr2)
    path-prop-implies-path-isg pr1 pr2 p subgr1 subgr2 = any-isg-with-same-prop-are-equal (transport is-subgrp p subgr1) subgr2

    subgrp'= : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) (pt : (transport is-subgrp p (Σ.snd a)) == (Σ.snd b)) → (a == b)
    subgrp'= (fst₁ , snd₁) (.fst₁ , .snd₁) idp idp = idp

    subgrp'-eq : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) → (a == b)
    subgrp'-eq a b p = subgrp'= a b p (path-prop-implies-path-isg (Σ.fst a) (Σ.fst b) p (Σ.snd a) (Σ.snd b))

    subgrp-subgrp'-equiv : (G : Group {α}) → Subgrp G ≃ subgrp' {G}
    subgrp-subgrp'-equiv G = f , (record { g = g ; f-g = f-g ; g-f = g-f ; adj = λ a → idp })
      where
        f : Subgrp G → subgrp' {G}
        f record { prop = prop ; f = f ; id = id ; comp = comp ; inv = inv } = prop , record {f = λ a → f {a} ; id = id; comp = λ a b → comp {a} {b}; inv = λ a → inv {a}}

        g : subgrp' {G} → Subgrp G
        g (prop , record { f = f ; id = id ; comp = comp ; inv = inv }) = record{ prop = prop ; f = λ {a} → f a ; id = id ; comp = λ {a} {b} → comp a b ; inv = λ {a} → inv a}

        f-g : (b : subgrp') → f (g b) == b
        f-g b = idp

        g-f : (a : Subgrp G) → g (f a) == a
        g-f a = idp

  subgrp-eq : {G : Group {α}} {a b : Subgrp G} (p : Subgrp.prop a == Subgrp.prop b) → (a == b)
  subgrp-eq {G} {a} {b} p = path
    where
      open is-equiv (Σ.snd (subgrp-subgrp'-equiv G))
      f : Subgrp G → subgrp' {G}
      f = Σ.fst (subgrp-subgrp'-equiv G)

      prf : ((f a) == (f b))
      prf = subgrp'-eq (f a) (f b) p

      path : (a == b)
      path =
        a  =⟨ ! (g-f a) ⟩
        g(f(a)) =⟨ ap g prf ⟩
        g(f(b)) =⟨ g-f b ⟩
        b =∎


apd2 : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd2 f idp = idp

{- We show in this module that if you have a map f from groups to subgroups, a particular
   group G and any automorphism between G, then there is a path between the subgroup (f G)
   and the subgroup obtained by applying that automorphism to (f G) -}
module _  (f : (G : Group {α}) → (Subgrp G)) where

  private
    lift-aut-lemma1 : {G H : Group} (p : G == H) → (lift-iso-over-subgrp (idtoiso p)) == (transport Subgrp  p)
    lift-aut-lemma1 {G} {H} idp =
      lift-iso-over-subgrp (idtoiso idp) =⟨ ap lift-iso-over-subgrp idtoiso-idp-equiv ⟩
      lift-iso-over-subgrp (idtoiso' idp) =⟨ λ= (λ g → subgrp-eq idp) ⟩
      transport Subgrp idp =∎


    lift-aut-lemma2 : {G : Group} (aut : G ≃ᴳ G) → lift-iso-over-subgrp aut == transport Subgrp (isotoid aut)
    lift-aut-lemma2 {G} aut =
        lift-iso-over-subgrp aut =⟨ ap lift-iso-over-subgrp (! (iso-id-equiv {G} {G} aut)) ⟩
        lift-iso-over-subgrp (idtoiso (isotoid aut)) =⟨ lift-aut-lemma1 ((isotoid aut)) ⟩
        transport Subgrp (isotoid aut) =∎

  lift-aut-retains-subgrp : {G : Group} (aut : G ≃ᴳ G) → ((lift-iso-over-subgrp aut (f G)) == f G)
  lift-aut-retains-subgrp {G} aut =  funqeq (lift-aut-lemma2 aut) (f G) ∙ (apd2 f (isotoid aut))


module ConjAut {G : Group {α}} where

  private 

    open Group G
    conj-map : (a : U) → (U → U)
    conj-map a g = a · (g · (i a))

    conj-map-inv : (a : U) → (conj-map a) ∘ (conj-map (i a)) == idf U
    conj-map-inv a = λ= (λ x →
      (conj-map a (conj-map (i a) x)) =⟨ idp ⟩
      a · (( (i a) · (x · (i (i a))) ) · (i a)) =⟨ ! (associative a ((i a) · (x · (i (i a)))) (i a)) ⟩
      (a · ( (i a) · (x · (i (i a))) )) · (i a) =⟨ ap (λ y → y · (i a)) (! (associative a (i a) (x · (i (i a))))) ⟩
      (( a · (i a)) · (x · (i (i a))) ) · (i a) =⟨ ap (λ y → (y · (x · (i (i a))) ) · (i a)) (inv-r a) ⟩
      (e · (x · (i (i a))) ) · (i a) =⟨ ap (λ y → y · (i a)) (unit-l (x · (i (i a)))) ⟩
      (x · (i (i a))) · (i a) =⟨ associative x (i (i a)) (i a) ⟩
      x · ((i (i a)) · (i a)) =⟨ ap (λ y → x · y) (inv-l (i a)) ⟩
      x · e =⟨ unit-r x ⟩
      x =∎)

    module _ (a : Group.U G) where

      conj-map-is-hom : (g₁ g₂ : U) → conj-map a (g₁ · g₂) == ((conj-map a g₁) · (conj-map a g₂))
      conj-map-is-hom g₁ g₂ =
        a · ((g₁ · g₂) · (i a)) =⟨ ap (λ ϕ → a · ϕ) (associative g₁ g₂ (i a)) ⟩
        a · (g₁ · (g₂ · (i a))) =⟨ ap (λ ϕ → a · (g₁ · ϕ)) (! (unit-l ((g₂ · (i a))))) ⟩
        a · (g₁ · ( e · (g₂ · (i a)))) =⟨ ap (λ ϕ → a · (g₁ · (ϕ · (g₂ · (i a))))) (! (inv-l a)) ⟩
        a · (g₁ · (((i a) · a ) · (g₂ · (i a)))) =⟨ ap (λ ϕ → a · (g₁ · ϕ) ) (associative (i a) a (g₂ · (i a))) ⟩
        a · (g₁ · ((i a) ·(a · (g₂ · (i a))))) =⟨ ap (λ ϕ → a · ϕ) (! (associative g₁ ((i a)) ((a · (g₂ · (i a)))))) ⟩
        a · ((g₁ · (i a)) ·(a · (g₂ · (i a)))) =⟨ ! (associative a ((g₁ · (i a))) ((a · (g₂ · (i a))))) ⟩
        (a · (g₁ · (i a))) ·(a · (g₂ · (i a))) =∎

      conj-hom : GroupHom G G
      conj-hom = group-hom (conj-map a) conj-map-is-hom


      conj-hom-g-f : (b : U) → (conj-map (i a) (conj-map a b)) == b
      conj-hom-g-f b =
        conj-map (i a) (conj-map a b) =⟨ ap (λ ϕ → conj-map (i a) (conj-map ϕ b)) (! (inv-inv-is-unit a)) ⟩
        conj-map (i a) (conj-map (i (i a)) b) =⟨ funqeq (conj-map-inv (i a)) b ⟩
        b =∎

      conj-hom-is-equiv : is-equiv (conj-map a)
      conj-hom-is-equiv = is-eq (conj-map a) (conj-map (i a)) (λ b → funqeq (conj-map-inv a) b) (conj-hom-g-f)

  conj-aut : (a : U) → G ≃ᴳ G
  conj-aut a = conj-hom a , conj-hom-is-equiv a

{- Based on the previous module we can now give an alternative definition of normal subgroups that suits are pruposes well, namely we define a subgroup to be normal if the lifted conjugation automorphims map the subgroup onto itself -}
is-normal' : {G : Group {α}} (H : Subgrp G) → Set (lsucc α)
is-normal' {G} H = (a : Group.U G) → (lift-iso-over-subgrp {G} {G} (ConjAut.conj-aut a) H) == H

{- This should be equivalent to the usual definition of normal subgroups that we defined in the group-basics file. For our purposes it is sufficient to show that is-normal' implies is-normal. We will do so in the next module -}
module normal-to-normal' {G : Group {α}} {H : Subgrp G} where

  open Group G
  open Subgrp

  private 
  {- the following function takes the subgroup H < G and produces for an element (a : G) the conjugated subgroup aH(i a), that is, it applies the lifted conjugation automorphism to the subgroup. We denote this as φₐ[H] where φₐ : G → G : x ↦ a · x · (i a) -}
    conj-subgr : (a : U) → Subgrp G
    conj-subgr a =  lift-iso-over-subgrp (ConjAut.conj-aut {G} a) H

    {- Here we show that if two groups G and G' are isomorphic, the isomorphism preserves subgroups. Basically we prove that map-lift of an isomorphism does exactly what it is supposed to do  -}
    iso-lift-prop-comp : {G' : Group {α}} → (iso : G ≃ᴳ G') → (h : U) → prop H h → prop ((lift-iso-over-subgrp iso) H) ((GroupHom.f (fst iso)) h)
    iso-lift-prop-comp iso h proph = coe (ap (prop H) (! (is-equiv.g-f (snd iso) h))) proph
  
    {- As a specific instance of the previous lemma, we can show that φₐ[H], the subgroup H lifted over the conjugacy automorphism (conj-aut a), contains all the elements of the form a · h · (i a) for h in H-}
    lift-subgr-conj : (a : U) → (h : U) → prop H h → prop (conj-subgr a) (a · (h · (i a)))
    lift-subgr-conj a h proph = iso-lift-prop-comp {G} (ConjAut.conj-aut {G} a ) h proph

    {- The following are two obvious auxiliary lemma's that will be useful -} 
    eq-subgrps-have-eq-props : {N : Subgrp G} → (p : N == H) → (prop N == prop H) 
    eq-subgrps-have-eq-props idp = idp
  
    eq-props-elts : {N : Subgrp G} → (p : prop N == prop H) → (a : U) → (prop N a) → (prop H a)
    eq-props-elts {N = record { prop = prop ; f = f ; id = id ; comp = comp ; inv = inv }} idp a = coe idp

  {- We can now prove that is-normal' implies is-normal. We are given elements (a : G) and (h : H) and we want to prove that a · h · (i a) is in H. Using (is-normal' a) we have a proof that φₐ[H] == H as subgroups of G, where φₐ : G → G : x ↦ a · x · (ia) is the conjugation map for a. Therefore, their props are equal, and from the 'lift-subgr-conj' lemma we can deduce that a · h · (i a) is in φₐ[H], hence we can conclude that it is also in H -}
  is-normal'-to-is-normal : is-normal' H → is-normal H
  is-normal'-to-is-normal Hnorm' = λ a h proph →  eq-props-elts {conj-subgr a} (eq-subgrps-have-eq-props (Hnorm' a)) ((a · (h · (i a)))) (lift-subgr-conj a h proph)


{- Finally, we prove the second goal of the project in two steps -}
{- Firstly, we show that definable subgroups are normal', according to our alternative defition of normal subgroups. This follows straight from the machinery that we set up earlier in the file, namely the fact that for all group isomorphism φ : G → H we have φ[f G] == f G. In particular, we can apply this to the conjugation automorphisms that we are using in our alternative definition of is-normal' -}
def-subgroups-are-normal' : (f : (G : Group {α}) → (Subgrp G)) → (G' : Group {α}) → (is-normal' (f G'))
def-subgroups-are-normal' f G' =  λ a → lift-aut-retains-subgrp f (ConjAut.conj-aut a)

{- Lastly, using the is-normal-to-is-normal' function that we set up in the previous module we can prove our final goal, that all definable subgroups are normal in HoTT -}
def-subgroups-are-normal : (f : (G : Group {α}) → (Subgrp G)) → (G' : Group {α}) → (is-normal (f G'))
def-subgroups-are-normal f G' = normal-to-normal'.is-normal'-to-is-normal {G'} {f G'} (def-subgroups-are-normal' f G')
