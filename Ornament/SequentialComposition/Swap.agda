open import Thesis.Prelude.Category
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.Category
open import Thesis.Ornament.RefinementSemantics

open import Data.Product using (_,_)

open Category Fam using () renaming (_·_ to _·Fam_; _≈_ to _≈Fam_; id to idFam)

module Thesis.Ornament.SequentialComposition.Swap
  {I J K L : Set} {e : J → I} {f : K → I} {g : L → e ⋈ f} {D E F G}
  (O : Orn e D E) (P : Orn f D F) (Q : Orn g ⌊ O ⊗ P ⌋ G) (r : FamMorphism (_ , μ ⌊ O ⊗ P ⌋) (_ , μ G))
  (r-inverse-l : r ·Fam (g , forget Q) ≈Fam idFam) (r-inverse-r : (g , forget Q) ·Fam r ≈Fam idFam) where

open import Thesis.Prelude.Category.Isomorphism.Functor
open import Thesis.Prelude.Category.Isomorphism.Midpoint
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Category.Span
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function
open import Thesis.Refinement
open import Thesis.Description
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.ParallelComposition.Pullback

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open Functor

private

  fullIso : Iso (SliceCategory Fam (object Ind (I , D)))
                (object (SliceMap Ind) (slice _ (_ , ⌈ O ⊗ P ⌉ ⊙ Q)))
                (object (SliceMap Ind) (slice _ (_ , ⌈ O ⊗ P ⌉)))
  fullIso =
    record { to   = sliceMorphism (g , forget Q) (frefl , ≐-to-≑ (fsym (forget-after-forget ⌈ O ⊗ P ⌉ Q)))
           ; from = sliceMorphism r
                      (begin
                         (_ , forget (⌈ O ⊗ P ⌉ ⊙ Q)) ·Fam r
                           ≈⟨ Category.cong-r Fam r (frefl , (≐-to-≑ (forget-after-forget ⌈ O ⊗ P ⌉ Q))) ⟩
                         (_ , λ {jk} → forget ⌈ O ⊗ P ⌉ {jk}) ·Fam (g , forget Q) ·Fam r
                           ≈⟨ Category.cong-l Fam (_ , forget ⌈ O ⊗ P ⌉) r-inverse-r ⟩
                         (_ , forget ⌈ O ⊗ P ⌉)
                       □)
           ; to-from-inverse = r-inverse-r
           ; from-to-inverse = r-inverse-l }
    where open EqReasoning (Category.Morphism Fam (_ , μ ⌊ O ⊗ P ⌋) (_ , μ D)) renaming (_∎ to _□)

  famIso : Iso Fam (_ , μ (OptPD (⌈ O ⊗ P ⌉ ⊙ Q))) (_ , μ (OptPD ⌈ O ⊗ P ⌉))
  famIso = iso-preserving SliceU
             (midpoint-iso (SliceCategory Fam (object Ind (I , D)))
                           (object (SliceMap Ind) (slice _ (_ , ⌈ O ⊗ P ⌉ ⊙ Q)))
                           (object (SliceMap Ind) (slice _ (_ , ⌈ O ⊗ P ⌉)))
                           (object (SliceMap Ind) (slice _ (_ , ⌈ singOrn D ⌉)))
                           fullIso
                           (proj₁ (proj₁ (⊗-is-Pullback (⌈ O ⊗ P ⌉ ⊙ Q) ⌈ singOrn D ⌉))) (proj₂ (⊗-is-Pullback (⌈ O ⊗ P ⌉ ⊙ Q) ⌈ singOrn D ⌉))
                           (proj₁ (proj₁ (⊗-is-Pullback ⌈ O ⊗ P ⌉ ⌈ singOrn D ⌉))) (proj₂ (⊗-is-Pullback ⌈ O ⊗ P ⌉ ⌈ singOrn D ⌉)))

⊗-⊙-FSwap : FSwap (RSem' ⌈ O ⊗ P ⌉) → FSwap (RSem' (⌈ O ⊗ P ⌉ ⊙ Q))
⊗-⊙-FSwap s =
  wrap λ { {._} (ok l) →
           record { Q = Swap.Q (FSwap.comp s (ok (g l)))
                  ; s = λ x → Setoid.trans (IsoSetoid Fun) (compIso famIso (ok l , ok (_ , x))) (Swap.s (FSwap.comp s (ok (g l))) x) } }