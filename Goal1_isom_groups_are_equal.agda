{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.NType
open import lib.NType2
open import lib.Funext
open import lib.PathOver
open import lib.types.Sigma
open import lib.types.Pi
open import lib.PathGroupoid
open import lib.Univalence

open import Group-basics
open import Magma-basics

module Goal1_isom_groups_are_equal where

open Group-basics.Properties
{- In this file we work towards the first goal of the project: isomorphisms
   between groups are equivalent to identities between groups in HoTT.

   The plan is to show that isomorphisms between groups are equivalent to some
   simpler notion of equivalence between a sigma type which is equiavelent to
   our notion of groups.

   As it stands it seems sufficient to show that the underlying magma of two
   groups is equal, then the other properties follow, i.e., is-group is a
   proposition. So for two groups to be equaivalent it is enough to have the
   underlying magma to be equivalent.
-}

module _ {α : ULevel} {M : Magma {α}} where
  open Magma M

  {- We want the proofs that a Magma is a group to be propositions. -}
  is-group-all-paths : (x y : is-group M) → (x == y)
  is-group-all-paths (isAssoc , isSet , (e , isUnit) , inv , isInv)
        (isAssoc' , isSet' , (e' , isUnit') , inv' , isInv')
        =   pair×= isAssoc= (pair×= isSet= (pair= unit= ↓-inv=))
    where
      module G = Group (group M (isAssoc , isSet , (e , isUnit) , inv , isInv))
      module H = Group (group M (isAssoc' , isSet' , (e' , isUnit') , inv'
                                                                    , isInv'))

      paths-are-props : {a b : X} → is-prop (a == b)
      paths-are-props {a} {b} = has-level-apply isSet a b

      isSet= : isSet == isSet'
      isSet= = prop-has-all-paths isSet isSet'

      isAssoc= : isAssoc == isAssoc'
      isAssoc= = ap (curry ∘ curry) (λ= λ {((a , b) , c) →
        prop-path paths-are-props (isAssoc a b c) (isAssoc' a b c)})

      H= : _∗_ == H.comp
      H= = idp

      e= : e == e'
      e= =
          e
        =⟨ ! (H.unit-r e) ⟩
          e ∗ e'
        =⟨ G.unit-l e' ⟩
          e'
        =∎

      isUnit= : isUnit == isUnit' [ (λ x → is-unit-l _∗_ x) ↓ e= ]
      isUnit= = from-transp ((λ x → is-unit-l _∗_ x)) e= {isUnit} (λ= (λ x →
        prop-path paths-are-props (
          (transport ((λ x → is-unit-l _∗_ x)) e= isUnit) x) (isUnit' x)))

      unit= : (e , isUnit) == (e' , isUnit')
      unit= = pair= e= isUnit=

      inv= : inv == inv'
      inv= = λ= (λ x →
          inv x
        =⟨ ! (H.unit-r (inv x)) ⟩
          (inv x) ∗ e'
        =⟨ ap (λ φ → (inv x) ∗ φ) (! (H.inv-r x)) ⟩
          (inv x) ∗ (x ∗ (inv' x))
        =⟨ ! (G.associative (inv x) x (inv' x)) ⟩
          ((inv x) ∗ x) ∗ (inv' x)
        =⟨ ap (λ φ → (φ ∗ inv' x)) (G.inv-l x) ⟩
          e ∗ inv' x
        =⟨ G.unit-l (inv' x) ⟩
          inv' x
        =∎)

      ↓-inv= : (inv , isInv) == (inv' , isInv')
                            [ (λ { (x , isU) → has-inverse-l _∗_ x}) ↓ unit= ]
      ↓-inv= = from-transp (λ x → has-inverse-l _∗_ (fst x)) unit= (inv,isInv= {unit=})
        where
          tpinv : (p : e , isUnit == e' , isUnit') → has-inverse-l _∗_ e'
          tpinv p = transport (λ x → has-inverse-l _∗_ (fst x)) p (inv , isInv)

          inv1= : (p : e , isUnit == e' , isUnit') → fst (tpinv p) == inv'
          inv1= idp = λ= (λ x →
              inv x
            =⟨ ap (λ f → f x) inv= ⟩
              inv' x
            =∎)

          is-inverse-l-is-prop : {inv : X → X} {e : X}
                               → is-prop (is-inverse-l _∗_ e inv)
          is-inverse-l-is-prop {inv} {e} = all-paths-is-prop (λ f g →
            λ= (λ x → prop-path paths-are-props (f x) (g x)))

          inv2= : (p : e , isUnit == e' , isUnit') → snd {α} (tpinv p) == isInv'
                                  [ (λ x → is-inverse-l _∗_ e' x) ↓ inv1= p ]
          inv2= idp = from-transp (λ x → is-inverse-l _∗_ e' x) (inv1= idp)
                                  (prop-path is-inverse-l-is-prop (transport
                                    (λ x → is-inverse-l _∗_ e' x) (inv1= idp)
                                    (snd {α} (tpinv idp)))
                                  isInv')

          inv,isInv= : {p : e , isUnit == e' , isUnit'}
                     → (tpinv p) == (inv' , isInv')
          inv,isInv= {p} = pair= (inv1= p) (inv2= p)

  is-group-is-prop : is-prop (is-group M)
  is-group-is-prop = all-paths-is-prop is-group-all-paths

module _ {α : ULevel} where
  private

    Group' : Type (lsucc α)
    Group' = Σ Magma (λ X → (is-group X))

    Σ⟪_⟫ : Group → Group'
    Σ⟪ group M is-group ⟫ = M , is-group

    -Σ⟪_⟫ : Group' → Group
    -Σ⟪ M , is-group ⟫ = group M is-group

    Group≃Group' : Group {α} ≃ Group'
    Group≃Group' = equiv f g f-g g-f
      where
        f : Group → Group'
        f G = Σ⟪ G ⟫

        g : Group' → Group
        g G = -Σ⟪ G ⟫

        f-g : (G : Group') → (f (g G) == G)
        f-g (fst₁ , snd₁) = idp

        g-f : (G : Group) → (g (f G) == G)
        g-f M = idp

    {- We define a notion of group' equivalence. -}
    group'= : (G H : Group') → Type α
    group'= G H = magma= (fst G) (fst H)

    {- This notion should be equivalent to isomorphism. -}
    iso≃group'= : (G H : Group) → (G ≃ᴳ H) ≃ (group'= Σ⟪ G ⟫ Σ⟪ H ⟫)
    iso≃group'= G H = equiv f g f-g g-f
      where

        X≃ : G ≃ᴳ H → (Magma.X (fst Σ⟪ G ⟫) ≃ Magma.X (fst Σ⟪ H ⟫))
        X≃ iso = GroupHom.f (fst iso) , snd iso

        f : G ≃ᴳ H → group'= Σ⟪ G ⟫ Σ⟪ H ⟫
        f x = record { carrier-equiv = X≃ x
                     ; preserves-operator = GroupHom.pres-comp (fst x) }

        g : group'= Σ⟪ G ⟫ Σ⟪ H ⟫ → G ≃ᴳ H
        g record { carrier-equiv = carrier-equiv
                 ; preserves-operator = preserves-operator }
               = (group-hom (–> carrier-equiv) preserves-operator) , snd carrier-equiv

        f-g : (x : group'= Σ⟪ G ⟫ Σ⟪ H ⟫) → f (g x) == x
        f-g x = idp

        g-f : (x : G ≃ᴳ H) → g (f x) == x
        g-f x = idp

  magma-id≃group'-id : {G H : Group {α}} → (Group.M G == Group.M H) ≃ (Σ⟪ G ⟫ == Σ⟪ H ⟫)
  magma-id≃group'-id {G} {H} = equiv f g f-g g-f
    where
      f : {G H : Group {α}} → (Group.M G == Group.M H) → (Σ⟪ G ⟫ == Σ⟪ H ⟫)
      f x = pair= x (from-transp (λ m → is-group m) x (prop-path is-group-is-prop _ _))

      g : {G H : Group {α}} → (Σ⟪ G ⟫ == Σ⟪ H ⟫) → (Group.M G == Group.M H)
      g = fst=

      f-g : {G H : Group {α}} → (b : Σ⟪ G ⟫ == Σ⟪ H ⟫) → f (g b) == b
      f-g {group M is-group} {group .M .is-group} idp =
          f (g {group M is-group} idp)
        =⟨ pair== idp (prop-path (has-level-apply (prop-is-set is-group-is-prop) _ _) _ _) ⟩
          idp
        =∎

      g-f : {G H : Group {α}} → (a : Group.M G == Group.M H) → g {G} {H} (f a) == a
      g-f {group M x} {group .M y} idp = fst=-β idp (from-transp is-group idp
        (prop-path (has-level-in (has-level-apply is-group-is-prop)) x y))

  {- Now we want to show that isomorphisms are equivalent to equalities between
     groups. -}
  iso≃id : {G H : Group {α}} → (G ≃ᴳ H) ≃ (G == H)
  iso≃id {G} {H} =
      G ≃ᴳ H
    ≃⟨ iso≃group'= G H ⟩
      group'= Σ⟪ G ⟫ Σ⟪ H ⟫
    ≃⟨ magma=-equiv (Group.M G) (Group.M H) ⟩
      Group.M G == Group.M H
    ≃⟨ magma-id≃group'-id ⟩
      Σ⟪ G ⟫ == Σ⟪ H ⟫
    ≃⟨ ap-equiv (Group≃Group' ⁻¹) Σ⟪ G ⟫ Σ⟪ H ⟫ ⟩
      G == H
    ≃∎

  idtoiso : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
  idtoiso = <– iso≃id

  isotoid : {G H : Group {α}} (iso : G ≃ᴳ H) → (G == H)
  isotoid = –> iso≃id

  idtoiso' : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
  idtoiso' {G} {.G} idp = →ᴳ-id , is-eq (λ z → z) (λ z → z) (λ a → idp) (λ a → idp)

  iso-equiv : {G H : Group {α}} → {iso₁ iso₂ : G ≃ᴳ H} → (p : (GroupHom.f (Σ.fst iso₁)) == (GroupHom.f (Σ.fst iso₂))) → iso₁ == iso₂
  iso-equiv p = {!!}

  test-lemma2 : {G : Group {α}} → GroupHom.f (Σ.fst (idtoiso {G} idp)) == (coe idp)
  test-lemma2 {G} = ap (λ φ → coe (ap fst (ap (fst magma-equiv) (ap fst φ)))) (!-inv-l ((is-equiv.g-f (is-equiv-inverse (snd Group≃Group')) Σ⟪ G ⟫)))

  idtoiso-equiv : {G H : Group {α}} → idtoiso {G} {H} == idtoiso' {G} {H}
  idtoiso-equiv {G} {H} = λ= (λ a → lemma a)
    where
      lemma : (a : G == H) → idtoiso a == idtoiso' a
      lemma idp = iso-equiv (test-lemma2 {G})

