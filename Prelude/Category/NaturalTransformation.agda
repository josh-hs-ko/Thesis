module Thesis.Prelude.Category.NaturalTransformation where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism

open import Level
open import Data.Product using (Σ; _,_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Functor


inverse-naturality :
  {ℓ₀ ℓ₁ ℓ₂ : Level} {C D : Category {ℓ₀} {ℓ₁} {ℓ₂}} {F G : Functor C D}
  (t : NatTrans F G) (isos : ∀ X → PartOfIso D (NatTrans.comp t X)) →
  ∀ {X Y} (f : Category._==>_ C X Y) →
  Category._≈_ D (Category._·_ D (morphism F f) (PartOfIso.from D (isos X)))
                 (Category._·_ D (PartOfIso.from D (isos Y)) (morphism G f))
inverse-naturality {D = D} {F} {G} t isos {X} {Y} f =
  begin
    morphism F f · PartOfIso.from D (isos X)
      ≈⟨ Setoid.sym (Morphism (object G X) (object F Y)) (cong-r (PartOfIso.from D (isos X)) (id-l (morphism F f))) ⟩
    (id · morphism F f) · PartOfIso.from D (isos X)
      ≈⟨ Setoid.sym (Morphism (object G X) (object F Y))
           (cong-r (PartOfIso.from D (isos X)) (cong-r (morphism F f) (PartOfIso.from-to-inverse D (isos Y)))) ⟩
    ((PartOfIso.from D (isos Y) · NatTrans.comp t Y) · morphism F f) · PartOfIso.from D (isos X)
      ≈⟨ cong-r (PartOfIso.from D (isos X)) (assoc (PartOfIso.from D (isos Y)) (NatTrans.comp t Y) (morphism F f)) ⟩
    (PartOfIso.from D (isos Y) · (NatTrans.comp t Y · morphism F f)) · PartOfIso.from D (isos X)
      ≈⟨ Setoid.sym (Morphism (object G X) (object F Y))
           (cong-r (PartOfIso.from D (isos X)) (cong-l (PartOfIso.from D (isos Y)) (NatTrans.naturality t f)))  ⟩
    (PartOfIso.from D (isos Y) · (morphism G f · NatTrans.comp t X)) · PartOfIso.from D (isos X)
      ≈⟨ Setoid.sym (Morphism (object G X) (object F Y))
           (cong-r (PartOfIso.from D (isos X)) (assoc (PartOfIso.from D (isos Y)) (morphism G f) (NatTrans.comp t X)))⟩
    ((PartOfIso.from D (isos Y) · morphism G f) · NatTrans.comp t X) · PartOfIso.from D (isos X)
      ≈⟨ assoc (PartOfIso.from D (isos Y) · morphism G f) (NatTrans.comp t X) (PartOfIso.from D (isos X)) ⟩
    (PartOfIso.from D (isos Y) · morphism G f) · (NatTrans.comp t X · PartOfIso.from D (isos X))
      ≈⟨ cong-l (PartOfIso.from D (isos Y) · morphism G f) (PartOfIso.to-from-inverse D (isos X)) ⟩
    (PartOfIso.from D (isos Y) · morphism G f) · id
      ≈⟨ id-r (PartOfIso.from D (isos Y) · morphism G f) ⟩
    PartOfIso.from D (isos Y) · morphism G f
  ∎
  where open Category D
        open EqReasoning (Morphism (object G X) (object F Y))

toNatIso : {ℓ₀ ℓ₁ ℓ₂ : Level} {C D : Category {ℓ₀} {ℓ₁} {ℓ₂}} {F G : Functor C D}
           (t : NatTrans F G) → (∀ X → PartOfIso D (NatTrans.comp t X)) → Iso (Funct C D) F G
toNatIso {D = D} t isos =
  record { to   = t
         ; from = record { comp = λ X → PartOfIso.from D (isos X); naturality = inverse-naturality t isos }
         ; from-to-inverse = λ X → PartOfIso.from-to-inverse D (isos X)
         ; to-from-inverse = λ X → PartOfIso.to-from-inverse D (isos X) }