-- A sufficient condition for establishing an isomorphism between the two types related by a refinement.

module Refinement.Isomorphism where

open import Prelude.Equality
open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Function.Isomorphism
open import Prelude.InverseImage
open import Refinement

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; <_,_>)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) renaming (setoid to ≡-Setoid)


IsoRefinement : {X Y : Set} → Refinement X Y → Set
IsoRefinement {X} {Y} r = Σ[ existence ∶ (∀ x → Refinement.P r x) ] (∀ x → Unique (≡-Setoid _) (existence x))

toFunIso : {X Y : Set} → (r : Refinement X Y) → IsoRefinement r → Iso Fun X Y
toFunIso r (ex , un) =
  Setoid.sym (IsoSetoid Fun)
    (Setoid.trans (IsoSetoid Fun)
      (Refinement.i r)
      (record { to   = proj₁
              ; from = < id , ex >
              ; to-from-inverse = frefl
              ; from-to-inverse = λ { (x , p) → cong (_,_ x) (un x p) } }))

IsoFRefinement : {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} → FRefinement e X Y → Set
IsoFRefinement {I} {J} {e} r = PartOfIso Fun e × (∀ {i} (j : e ⁻¹ i) → IsoRefinement (FRefinement.comp r j))

memIso : {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} →
         (r : FRefinement e X Y) → IsoFRefinement r → ∀ {i} (j : e ⁻¹ i) → Iso Fun (X i) (Y (und j))
memIso r (_ , irs) j = toFunIso (FRefinement.comp r j) (irs j)

toFamIso : {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} (r : FRefinement e X Y) → IsoFRefinement r → Iso Fam (I , X) (J , Y)
toFamIso r (idx-iso , irs) =
  Setoid.sym (IsoSetoid Fam) (mkFamIso (toIso Fun idx-iso) (λ j → Setoid.sym (IsoSetoid Fun) (memIso r (idx-iso , irs) (ok j))))
