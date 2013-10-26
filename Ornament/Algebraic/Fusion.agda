-- Fold fusion theorems for algebraic ornamentation.

module Ornament.Algebraic.Fusion where


open import Prelude.Function
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.InverseImage
open import Description
open import Ornament
open import Ornament.Algebraic
open import Refinement
open import Relation
open import Relation.Fold

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)


algOrn-fusion-⊆ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊆ T • Ṙ D R →
  ∀ {i} {x} → μ ⌊ algOrn D S ⌋ (i , x) → ∀ {y} → (R !!) i x y → μ ⌊ algOrn D T ⌋ (i , y)
algOrn-fusion-⊆ D R S T fusion-condition {i} {x} d {y} r =
  Iso.from (Refinement.i rT)
    (forget ⌈ algOrn D S ⌉ d ,
     modus-ponens-⊆ (foldR-fusion-⊆ D R S T fusion-condition) i (forget ⌈ algOrn D S ⌉ d) y (x , proj₂ (Iso.to (Refinement.i rS) d) , r))
  where rS = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
        rT = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))

algOrn-fusion-⊇ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊇ T • Ṙ D R →
  ∀ {i} {y} → μ ⌊ algOrn D T ⌋ (i , y) → Σ[ x ∶ X i ] μ ⌊ algOrn D S ⌋ (i , x) × (R !!) i x y
algOrn-fusion-⊇ D R S T fusion-condition {i} {y} d
  with modus-ponens-⊆ (foldR-fusion-⊇ D R S T fusion-condition) i (forget ⌈ algOrn D T ⌉ d) y (proj₂ (Iso.to (Refinement.i rT) d))
  where rT = FRefinement.comp (toFRefinement (algOrn-FSwap D T)) (ok (i , y))
algOrn-fusion-⊇ D R S T fusion-condition {i} {y} d
  | x , s , r = x , Iso.from (Refinement.i rS) (forget ⌈ algOrn D T ⌉ d , s) , r
  where rS = FRefinement.comp (toFRefinement (algOrn-FSwap D S)) (ok (i , x))
