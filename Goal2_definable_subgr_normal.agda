{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.NType
open import lib.Funext
open import lib.types.Pi
open import Group-basics


{- In this file we work towards the second goal of the project: definable subgroups are normal in HoTT -}

module Goal2_definable_subgr_normal {α : ULevel} where

{- From a proof that two groups are equal (G == H), we obtain a map from Subgrp G to Subgrp H using transport -}
transp-subgrp : {G H : Group {α}} (p : G == H) → (Subgrp G) → (Subgrp H)
transp-subgrp p G' = transport Subgrp p G'

{- We now use another way of finding a map from Subgrp G to Subgrp H using the identity -}
{- firstly, we define the map idtoiso which takes an equality to an isomorphism in the trivial way -}
idtoiso : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
idtoiso {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)

{- We 'lift' this isomorphism resulting from p to a map Subgrp G → Subgrp H -}
idtoiso-subgrp : {G H : Group {α}} (p : G == H) → (Subgrp G) → (Subgrp H)
idtoiso-subgrp {G} {.G} idp G' = G' -- We can actually just case split!
-- idtoiso-subgrp {i} {G} {H} p G' = record { prop = λ x → Subgrp.prop G' (θ-inv(x)) ; f = Subgrp.f G' ; id = {! !} ; comp = {! p  !} }
  -- where
  --   module H = Group H
  --   module G = Group G
  --
  --   equiv : (G ≃ᴳ H) -- The equivalence
  --   equiv = idtoiso p
  --
  --   open GroupHom (Σ.fst equiv)
  --
  --   θ : (G.U → H.U)   -- The forward map of the equivalence
  --   θ = GroupHom.f (Σ.fst equiv)
  --
  --   open is-hae (is-equiv→is-hae θ (Σ.snd equiv))
  --
  --   θ-inv : (H.U → G.U)  -- The backward map of the equivalence
  --   θ-inv = g

{- We want to prove that the previous two functions Subgrp G → Subgrp H are homotopic -}
trans-equiv-idtoiso : (G H : Group) → transp-subgrp {G} {H} == idtoiso-subgrp {G} {H}
trans-equiv-idtoiso G H = λ= (λ {idp → idp})

-- (transport Subgroup p (f G)) == f G

! : {α : ULevel} {X : Type α} {x y : X} (p : x == y) → y == x
! idp = idp

apd2 : {l k : ULevel} {X : Set l} {Y : X → Set k} {x x' : X} (f : (x : X) → Y x) (p : x == x') → (transport Y p (f x) ) == f x'
apd2 f idp = idp

map-lift2 : {G : Group} {H : Group} (hom : H →ᴳ G) → (Subgrp G → Subgrp  H)
map-lift2 {G} {H} hom sub-g = record { prop = prop-lemma  ; f = λ {a} → f-lemma a ; id =  id-lemma ; comp =  λ {a} {b} → comp-lemma a b; inv = λ {a} → inv-lemma a}
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

map-lift : {G : Group} {H : Group} (iso : G ≃ᴳ H) → (Subgrp G → Subgrp  H)
map-lift {G} {H} iso sub-g = map-lift2 {G} {H} hom sub-g
  where
    hom : H →ᴳ G
    hom = _≃ᴳ_.g-hom iso


postulate
  isotoid : {G H : Group {α}} (iso : G ≃ᴳ H) → G == H
  iso-id-equiv : {G H : Group {α}} (iso : G ≃ᴳ H) → (idtoiso (isotoid iso)) == iso
  --some-lemma : {G H : Group} (f : (I : Group) → (Subgrp I)) (iso : H ≃ᴳ G) → ((map-lift (Σ.fst iso) (f G)) == f H)


funqeq : {β : ULevel} {A B : Set β} {f g : A → B} (p : f == g) (a : A) → (f a == g a)
funqeq idp a = idp

prop= : {G : Group {α}} (N M : Subgrp G) → Set (lsucc α)
prop= N M =  (Subgrp.prop N) == (Subgrp.prop M)

impl-to-expl : {β : ULevel} {A : Type α} {B : A → Type β} → (f : ({a : A} → B a)) → ((a : A) → B a)
impl-to-expl f = –> expose-equiv f

expl-to-impl : {β : ULevel} {A : Type α} {B : A → Type β} → (f : ((a : A) → B a)) → ({a : A} → B a)
expl-to-impl f {a} = f a

λ=-implicit : {β : ULevel} {A : Type α} {B : A → Type β} → {f g : ({a : A} → B a)} → ((a : A) → (f {a} == g {a})) → ((λ {x} → f {x}) == (λ {x} → g {x}))
λ=-implicit ext = ap expl-to-impl (λ= ext)

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


--=lemma2 : {G : Group {α}} {pr : (Group.U G) → Set α} (subgrp1 subgrp2 : is-subgrp {G} pr) (eq1 : (is-subgrp.f subgrp1) == (is-subgrp.f subgrp2)) → ⊤
--=lemma2 = {!!}

module _ where
  open is-subgrp

  =lemma2 : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) (eq1 : f isg1 == f isg2) (eq2 : id isg1 == id isg2) (eq3 : comp isg1 == comp isg2) (eq4 : inv isg1 == inv isg2) → (isg1 == isg2)
  =lemma2 record { f = .(f isg2) ; id = .(id isg2) ; comp = .(comp isg2) ; inv = .(inv isg2) } isg2 idp idp idp idp = idp

  =lemma : {G : Group {α}} {pr : (Group.U G) → Set α} (isg1 isg2 : is-subgrp {G} pr) → (isg1 == isg2)
  =lemma isg1 isg2 = =lemma2 isg1 isg2 f-eq id-eq comp-eq inv-eq
    where
      f-eq : f isg1 == f isg2
      f-eq = {!!}

      id-eq : id isg1 == id isg2
      id-eq = {!!}

      comp-eq : comp isg1 == comp isg2
      comp-eq = {!!}

      inv-eq : inv isg1 == inv isg2
      inv-eq = {!!}

sub= : {G : Group {α}} (pr1 pr2 : (Group.U G) → Set α) (p : pr1 == pr2) (subgr1 : is-subgrp {G} pr1) (subgr2 : is-subgrp {G} pr2) → (transport is-subgrp p subgr1 == subgr2)
sub= pr1 pr2 p subgr1 subgr2 = =lemma (transport is-subgrp p subgr1) subgr2

subgrp'= : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) (pt : (transport is-subgrp p (Σ.snd a)) == (Σ.snd b)) → (a == b)
subgrp'= (fst₁ , snd₁) (.fst₁ , .snd₁) idp idp = idp

subgrp'-eq : {G : Group {α}} (a b : subgrp' {G}) (p : Σ.fst a == Σ.fst b) → (a == b)
subgrp'-eq a b p = subgrp'= a b p (sub= (Σ.fst a) (Σ.fst b) p (Σ.snd a) (Σ.snd b))

module _ {G : Group {α}} where
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
    prf : ((f a) == (f b))
    prf = subgrp'-eq (f a) (f b) p

<<<<<<< HEAD
      comp= : comp == comp₁
      comp= = {!!}  -- We need to use a version of implicit function extensionality here, it is proved above but not working in this context yet. 
  
      inv= : inv == inv₁
      inv= = {!!}
=======
    path : (a == b)
    path =
      a  =⟨ ! (g-f a) ⟩
      g(f(a)) =⟨ ap g prf ⟩
      g(f(b)) =⟨ g-f b ⟩
      b =∎
>>>>>>> 2a1288d99b81fe169a155c2d96233864551ab15a


module definable-normal-proof  (f : (G : Group) → (Subgrp G)) where

  map-lift-path-lemma : {G H : Group} (p : G == H) → (map-lift (idtoiso p)) == (transport Subgrp  p)
  map-lift-path-lemma idp = λ= (λ g → subgrp-eq idp)

  map-lift-lemma : {G : Group} (aut : G ≃ᴳ G) → map-lift aut == transport Subgrp (isotoid aut)
  map-lift-lemma aut =
      map-lift aut =⟨ ap map-lift (! (iso-id-equiv aut)) ⟩
      map-lift (idtoiso (isotoid aut)) =⟨ map-lift-path-lemma ((isotoid aut)) ⟩
      transport Subgrp (isotoid aut) =∎

  final-result : {G : Group} (aut : G ≃ᴳ G) → ((map-lift aut (f G)) == f G)
  final-result {G} aut =  funqeq (map-lift-lemma aut) (f G) ∙ (apd2 f (isotoid aut))




{- We are working towards the following claim: all definable subgroups are normal -}
def-subgroups-are-normal : (f : (G : Group {α}) → (Subgrp G)) → (H : Group) → (is-normal (f H))
def-subgroups-are-normal f H g h hprop = {!   !}
