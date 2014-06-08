-- Fold fusion theorems for algebraic ornamentation.

open import Description
open import Relation

module Examples.FoldFusion {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) where

open import Prelude.Function
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.InverseImage
open import Ornament
open import Ornament.Algebraic
open import Refinement
open import Relation.Fold

open import Function using (id)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

upg-⊆ : Upgrade ({i : I} → μ D i → μ D i) ({i : I} {x : X i} →  μ ⌊ algOrn D S ⌋ (i , x) → {y : Y i} → (R !!) i x y → μ ⌊ algOrn D T ⌋ (i , y))
upg-⊆ = let refS : (i : I) (x : X i) → Refinement (μ D i) (μ ⌊ algOrn D S ⌋ (i , x))
            refS i x = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
            refT : (i : I) (y : Y i) → Refinement (μ D i) (μ ⌊ algOrn D T ⌋ (i , y))
            refT i y = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))
        in  ∀[[ i ∈ I ]] ∀⁺[[ x ∈ X i ]] refS i x ⇀ (∀⁺[[ y ∈ Y i ]] ∀⁺[ _ ∈ (R !!) i x y ] toUpgrade (refT i y))

FusionCondition-⊆ : Set
FusionCondition-⊆ = R • S ⊆ T • Ṙ D R

fusion-⊆ : FusionCondition-⊆ → {i : I} {x : X i} (d : μ D i) → foldR' S i d x → {y : Y i} → (R !!) i x y → foldR' T i d y
fusion-⊆ cond {i} {x} d ss {y} r = modus-ponens-⊆ (foldR-fusion-⊆ D R S T cond) i d y (x , ss , r)

algOrn-fusion-⊆ : FusionCondition-⊆ → {i : I} {x : X i} → μ ⌊ algOrn D S ⌋ (i , x) → {y : Y i} → (R !!) i x y → μ ⌊ algOrn D T ⌋ (i , y)
algOrn-fusion-⊆ cond = Upgrade.u upg-⊆ id (fusion-⊆ cond)

algOrn-fusion-⊆-coherence :
  (cond : FusionCondition-⊆) {i : I} {x : X i} (d : μ ⌊ algOrn D S ⌋ (i , x)) {y : Y i} (r : (R !!) i x y) →
  forget ⌈ algOrn D T ⌉ (algOrn-fusion-⊆ cond d r) ≡ forget ⌈ algOrn D S ⌉ d
algOrn-fusion-⊆-coherence cond d r = Upgrade.c upg-⊆ id (fusion-⊆ cond) (forget ⌈ algOrn D S ⌉ d) d refl r

upg-⊇ : Upgrade ({i : I} → μ D i → μ D i) ({i : I} {y : Y i} → μ ⌊ algOrn D T ⌋ (i , y) → Σ[ x ∈ X i ] μ ⌊ algOrn D S ⌋ (i , x) × (R !!) i x y)
upg-⊇ = let refS : (i : I) (x : X i) → Refinement (μ D i) (μ ⌊ algOrn D S ⌋ (i , x))
            refS i x = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
            refT : (i : I) (y : Y i) → Refinement (μ D i) (μ ⌊ algOrn D T ⌋ (i , y))
            refT i y = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))
        in  ∀[[ i ∈ I ]] ∀⁺[[ y ∈ Y i ]] refT i y ⇀ (Σ⁺[ x ∈ X i ] toUpgrade (refS i x) ×⁺ (R !!) i x y)

FusionCondition-⊇ : Set
FusionCondition-⊇ = R • S ⊇ T • Ṙ D R

fusion-⊇ : FusionCondition-⊇ → {i : I} {y : Y i} (d : μ D i) → foldR' T i d y → Σ[ x ∈ X i ] foldR' S i d x × (R !!) i x y
fusion-⊇ cond {i} {y} d ts = modus-ponens-⊆ (foldR-fusion-⊇ D R S T cond) i d y ts

algOrn-fusion-⊇ : FusionCondition-⊇ → {i : I} {y : Y i} → μ ⌊ algOrn D T ⌋ (i , y) → Σ[ x ∈ X i ] μ ⌊ algOrn D S ⌋ (i , x) × (R !!) i x y
algOrn-fusion-⊇ cond = Upgrade.u upg-⊇ id (fusion-⊇ cond)

algOrn-fusion-⊇-coherence :
  (cond : FusionCondition-⊇) {i : I} {y : Y i} (d : μ ⌊ algOrn D T ⌋ (i , y)) →
  let (x , d' , r) = algOrn-fusion-⊇ cond d in forget ⌈ algOrn D S ⌉ d' ≡ forget ⌈ algOrn D T ⌉ d
algOrn-fusion-⊇-coherence cond d = Upgrade.c upg-⊇ id (fusion-⊇ cond) (forget ⌈ algOrn D T ⌉ d) d refl
