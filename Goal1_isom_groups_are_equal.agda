{-# OPTIONS --without-K --rewriting #-}
open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
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

  {- Fist we proof that the proofs that a specific Magma is a group are
     propositions.
  -}

  {- This boils down to showing that for all pairs of is-group M there is a
     path between them.
  -}
  is-group-all-paths : (x y : is-group M) → (x == y)
  is-group-all-paths (isAssoc , isSet , (e , isUnit) , inv , isInv)
        (isAssoc' , isSet' , (e' , isUnit') , inv' , isInv')
        =   pair×= isAssoc= (pair×= isSet= (pair= unit= inv=))
    where
      module G = Group (group M (isAssoc , isSet , (e , isUnit) , inv , isInv))
      module H = Group (group M (isAssoc' , isSet' , (e' , isUnit') , inv'
                                                                    , isInv'))
      {- Essentially, we need to show that all properties are equal under
         the assumption that the underlying Magma is equal. Most equalities
         follow trivially.  -}
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

      {- The inverse equality is trickier because it depends on the unit. In
         essence we need to transport the identies given the unit equality.
      -}
      inv= : (inv , isInv) == (inv' , isInv')
                            [ (λ { (x , isU) → has-inverse-l _∗_ x}) ↓ unit= ]
      inv= = from-transp (λ x → has-inverse-l _∗_ (fst x)) unit= (inv,isInv= {unit=})
        where
          {- First, We show that the inverse functions must actually be
            identical.
          -}
          inv=inv' : inv == inv'
          inv=inv' = λ= (λ x →
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

          {- We define a more convenient type for the transported inverse,
             because we will need to argue about it a lot. -}
          tpinv : (p : e , isUnit == e' , isUnit') → has-inverse-l _∗_ e'
          tpinv p = transport (λ x → has-inverse-l _∗_ (fst x)) p (inv , isInv)

          {- Now we show that the inverse functions must be equal after the
             transport.
          -}
          inv1= : (p : e , isUnit == e' , isUnit') → fst (tpinv p) == inv'
          inv1= idp = λ= (λ x →
              inv x
            =⟨ ap (λ f → f x) inv=inv' ⟩
              inv' x
            =∎)

          {- For the proof of the inverses we show that they are propositions.
          -}
          is-inverse-l-is-prop : {inv : X → X} {e : X}
                               → is-prop (is-inverse-l _∗_ e inv)
          is-inverse-l-is-prop {inv} {e} = all-paths-is-prop (λ f g →
            λ= (λ x → prop-path paths-are-props (f x) (g x)))

          {- Then we can easily show that the isInv must be equal. -}
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

  {- Thus, we can derive that is-groups are propositions. -}
  is-group-is-prop : is-prop (is-group M)
  is-group-is-prop = all-paths-is-prop is-group-all-paths

{- In this module we show the equivalence of isomorphisms and idenities. -}
module _ {α : ULevel} where
  {- We create a simple Sigma type based on our definition of Groups. -}
  private
    Group' : Type (lsucc α)
    Group' = Σ Magma (λ X → (is-group X))

    Σ⟪_⟫ : Group → Group'
    Σ⟪ group M is-group ⟫ = M , is-group

    -Σ⟪_⟫ : Group' → Group
    -Σ⟪ M , is-group ⟫ = group M is-group

    {- It follows trivially that the two types are equivalent. -}
    Group≃Group' : Group {α} ≃ Group'
    Group≃Group' = equiv f g f-g g-f
      where
        f : Group → Group'
        f G = Σ⟪ G ⟫

        g : Group' → Group
        g G = -Σ⟪ G ⟫

        f-g : (G : Group') → (f (g G) == G)
        f-g G = idp

        g-f : (G : Group) → (g (f G) == G)
        g-f M = idp

    {- We define a notion of group' equivalence. As we have seen before, the
       equality of group properties follows if the Magma's are equal. Hence,
       all we actually need is magma equivalence. -}
    group'= : (G H : Group') → Type α
    group'= G H = magma= (fst G) (fst H)

    {- Now we show that this notion is equivalent to isomorphism. -}
    iso≃group'= : (G H : Group) → (G ≃ᴳ H) ≃ (group'= Σ⟪ G ⟫ Σ⟪ H ⟫)
    iso≃group'= G H = equiv f g f-g g-f
      where
        f : G ≃ᴳ H → group'= Σ⟪ G ⟫ Σ⟪ H ⟫
        f x = record { carrier-equiv = GroupHom.f (fst x) , snd x
                     ; preserves-operator = GroupHom.pres-comp (fst x) }

        g : group'= Σ⟪ G ⟫ Σ⟪ H ⟫ → G ≃ᴳ H
        g record { carrier-equiv = carrier-equiv
                 ; preserves-operator = preserves-operator }
             = (group-hom (–> carrier-equiv) preserves-operator) ,
               snd carrier-equiv

        f-g : (x : group'= Σ⟪ G ⟫ Σ⟪ H ⟫) → f (g x) == x
        f-g x = idp

        g-f : (x : G ≃ᴳ H) → g (f x) == x
        g-f x = idp

  {- Next we show that magma identity is equivalent to group' identity. We can
     derive this from the fact that is-group is a proposition. -}
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

  {- Now we can show that isomorphisms are equivalent to equalities between
     groups.-}
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

  {- Then we get define the maps between group idenities and isomorphisms. -}
  idtoiso : {G H : Group {α}} → (G == H) → (G ≃ᴳ H)
  idtoiso = <– iso≃id

  isotoid : {G H : Group {α}} (iso : G ≃ᴳ H) → (G == H)
  isotoid = –> iso≃id

  {- This shows that the function of a underlying homomorphism of idtoiso of
     the identity path is the same as coe of idp. -}
  idtoiso-idp-gives-id-map : {G : Group {α}}
                           → GroupHom.f (fst (idtoiso {G} idp)) == (coe idp)
  idtoiso-idp-gives-id-map {G} =
     ap (λ φ → coe (ap fst (ap (fst magma-equiv) (ap fst φ))))
        (!-inv-l ((is-equiv.g-f (is-equiv-inverse (snd Group≃Group')) Σ⟪ G ⟫)))
