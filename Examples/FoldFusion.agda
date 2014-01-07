-- Fold fusion theorems for algebraic ornamentation.

module Examples.FoldFusion where


open import Prelude.Function
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.InverseImage
open import Description
open import Ornament
open import Ornament.Algebraic
open import Refinement
open import Relation
open import Relation.Fold

open import Function using (id)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)


algOrn-fusion-⊆ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊆ T • Ṙ D R →
  {i : I} {x : X i} {y : Y i} → μ ⌊ algOrn D S ⌋ (i , x) → (R !!) i x y → μ ⌊ algOrn D T ⌋ (i , y)
algOrn-fusion-⊆ D R S T fusion-condition {i} {x} {y} =
  Upgrade.u upg id (λ d ss r → modus-ponens-⊆ (foldR-fusion-⊆ D R S T fusion-condition) i d y (x , ss , r))
  where
    upg : Upgrade (μ D i → μ D i) (μ ⌊ algOrn D S ⌋ (i , x) → (R !!) i x y → μ ⌊ algOrn D T ⌋ (i , y))
    upg = let refS : Refinement (μ D i) (μ ⌊ algOrn D S ⌋ (i , x))
              refS = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
              refT : Refinement (μ D i) (μ ⌊ algOrn D T ⌋ (i , y))
              refT = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))
          in  refS ⇀ (∀⁺[ _ ∶ (R !!) i x y ] toUpgrade refT)

algOrn-fusion-⊇ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊇ T • Ṙ D R →
  {i : I} {y : Y i} → μ ⌊ algOrn D T ⌋ (i , y) → Σ[ x ∶ X i ] μ ⌊ algOrn D S ⌋ (i , x) × (R !!) i x y
algOrn-fusion-⊇ D {X} R S T fusion-condition {i} {y} = Upgrade.u upg id (λ d ts → modus-ponens-⊆ (foldR-fusion-⊇ D R S T fusion-condition) i d y ts)
  where
    upg : Upgrade (μ D i → μ D i) (μ ⌊ algOrn D T ⌋ (i , y) → Σ[ x ∶ X i ] μ ⌊ algOrn D S ⌋ (i , x) × (R !!) i x y)
    upg = let refS : (x : X i) → Refinement (μ D i) (μ ⌊ algOrn D S ⌋ (i , x))
              refS x = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
              refT : Refinement (μ D i) (μ ⌊ algOrn D T ⌋ (i , y))
              refT = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))
          in  refT ⇀ (Σ⁺[ x ∶ X i ] toUpgrade (refS x) ×⁺ (R !!) i x y)
