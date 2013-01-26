open import Thesis.Description
open import Thesis.Relation

module Thesis.Relation.GreedyTheorem
  {I : Set} (D : Desc I) {X : I → Set} (R : μ D ↝ μ D) (S : Ḟ D X ↝ X)
  (R-transitive : R • R ⊆ R) (monotonicity : α • Ṙ D R • α º ⊆ R)
  (Q : Ḟ D X ↝ Ḟ D X) (greedy-condition : (α • Ṙ D (foldR S º)) • Q º ⊆ R º • (α • Ṙ D (foldR S º))) where

open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Relation.Fold
open import Thesis.Relation.Hylomorphism
open import Thesis.Relation.Minimum
open import Thesis.Ornament
open import Thesis.Ornament.Algebraic
open import Thesis.Refinement

open import Function using (id)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning


H : X ↝ μ D
H = foldR {D = D} α • foldR S º

M : X ↝ μ D
M = min R •Λ H

first-obligation : α • Ṙ D M • min Q •Λ (S º) ⊆ H
first-obligation =
  begin
    α • Ṙ D (min R •Λ H) • min Q •Λ (S º)
      ⊆⟨ •-monotonic-l α (•-monotonic-r (min Q •Λ (S º)) (Ṙ-monotonic D (proj₁ (min-universal-⇒ ⊆-refl)))) ⟩
    α • Ṙ D H • min Q •Λ (S º)
      ⊆⟨ •-monotonic-l α (•-monotonic-l (Ṙ D H) (proj₁ (min-universal-⇒ ⊆-refl))) ⟩
    α • Ṙ D H • S º
      ⊆⟨ proj₂ (hylo-fixed-point D α S) ⟩
    H
  □
  where open PreorderReasoning (⊆-Preorder X (μ D)) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

second-obligation : (α • Ṙ D M • min Q •Λ (S º)) • H º ⊆ R
second-obligation =
  begin
    (α • Ṙ D M • min Q •Λ (S º)) • H º
      ⊆⟨ proj₁ (•-assoc α (Ṙ D M • min Q •Λ (S º)) (H º)) ⟩
    α • (Ṙ D M • min Q •Λ (S º)) • H º
      ⊆⟨ •-monotonic-l α (proj₁ (•-assoc (Ṙ D M) (min Q •Λ (S º)) (H º))) ⟩
    α • Ṙ D M • min Q •Λ (S º) • H º
      ⊆⟨ •-monotonic-l α (•-monotonic-r (min Q •Λ (S º) • H º) (Ṙ-monotonic D (min-monotonic ⊆-refl (foldR-α-lemma (foldR S º))))) ⟩
    α • Ṙ D (min R •Λ (foldR S º)) • min Q •Λ (S º) • H º
      ⊆⟨ proj₂ (•-assoc α (Ṙ D (min R •Λ (foldR S º))) (min Q •Λ (S º) • H º)) ⟩
    (α • Ṙ D (min R •Λ (foldR S º))) • min Q •Λ (S º) • H º
      ⊆⟨ •-monotonic-l (α • Ṙ D (min R •Λ (foldR S º)))
           (begin′
              min Q •Λ (S º) • H º
                ⊆⟨ proj₂ (º-preserves-comp H ((min Q •Λ (S º))º)) ⟩′
              (H • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-r ((min Q •Λ (S º))º) (proj₁ (hylo-fixed-point D α S))) ⟩′
              ((α • Ṙ D H • S º) • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-r (min Q •Λ (S º) º) (proj₂ (•-assoc α (Ṙ D H) (S º)))) ⟩′
              (((α • Ṙ D H) • S º) • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (proj₁ (•-assoc (α • Ṙ D H) (S º) ((min Q •Λ (S º))º))) ⟩′
              ((α • Ṙ D H) • S º • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-l (α • Ṙ D H) (proj₂ (º-preserves-comp (min Q •Λ (S º)) S))) ⟩′
              ((α • Ṙ D H) • (min Q •Λ (S º) • S)º) º
                ⊆⟨ º-monotonic (•-monotonic-l (α • Ṙ D H) (º-monotonic (proj₂ (min-universal-⇒ ⊆-refl)))) ⟩′
              ((α • Ṙ D H) • Q º) º
                ⊆⟨ º-monotonic (•-monotonic-r (Q º) (•-monotonic-l α (Ṙ-monotonic D (proj₁ (foldR-α-lemma (foldR S º)))))) ⟩′
              ((α • Ṙ D (foldR S º)) • Q º) º
                ⊆⟨ º-monotonic greedy-condition ⟩′
              (R º • α • Ṙ D (foldR S º)) º
                ⊆⟨ proj₁ (º-preserves-comp (R º) (α • Ṙ D (foldR S º))) ⟩′
              (α • Ṙ D (foldR S º)) º • R
                ⊆⟨ •-monotonic-r R (proj₁ (º-preserves-comp α (Ṙ D (foldR S º)))) ⟩′
              ((Ṙ D (foldR S º)) º • α º) • R
                ⊆⟨ proj₁ (•-assoc (Ṙ D (foldR S º) º) (α º) R) ⟩′
              (Ṙ D (foldR S º)) º • α º • R
                ⊆⟨ •-monotonic-r (α º • R) (proj₂ (Ṙ-preserves-conv D (foldR S º))) ⟩′
              Ṙ D (foldR S) • α º • R
            □′) ⟩
    (α • Ṙ D (min R •Λ (foldR S º))) • Ṙ D (foldR S) • α º • R
      ⊆⟨ proj₂ (•-assoc (α • Ṙ D (min R •Λ (foldR S º))) (Ṙ D (foldR S)) (α º • R)) ⟩
    ((α • Ṙ D (min R •Λ (foldR S º))) • Ṙ D (foldR S)) • α º • R
      ⊆⟨ •-monotonic-r (α º • R) (proj₁ (•-assoc α (Ṙ D (min R •Λ (foldR S º))) (Ṙ D (foldR S)))) ⟩
    (α • Ṙ D (min R •Λ (foldR S º)) • Ṙ D (foldR S)) • α º • R
      ⊆⟨ •-monotonic-r (α º • R) (•-monotonic-l α (proj₂ (Ṙ-preserves-comp D (min R •Λ (foldR S º)) (foldR S)))) ⟩
    (α • Ṙ D (min R •Λ (foldR S º) • foldR S)) • α º • R
      ⊆⟨ •-monotonic-r (α º • R) (•-monotonic-l α (Ṙ-monotonic D (proj₂ (min-universal-⇒ ⊆-refl)))) ⟩
    (α • Ṙ D R) • α º • R
      ⊆⟨ proj₂ (•-assoc (α • Ṙ D R) (α º) R) ⟩
    ((α • Ṙ D R) • α º) • R
      ⊆⟨ •-monotonic-r R (proj₁ (•-assoc α (Ṙ D R) (α º))) ⟩
    (α • Ṙ D R • α º) • R
      ⊆⟨ •-monotonic-r R monotonicity ⟩
    R • R
      ⊆⟨ R-transitive ⟩
    R
  □
  where open PreorderReasoning (⊆-Preorder (μ D) (μ D))   renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)
        open PreorderReasoning (⊆-Preorder (μ D) (Ḟ D X)) renaming (begin_ to begin′_; _∼⟨_⟩_ to _⊆⟨_⟩′_; _∎ to _□′)

M-prefix-point : α • Ṙ D M • min Q •Λ (S º) ⊆ M
M-prefix-point = min-universal-⇐ first-obligation second-obligation

greedy-theorem : foldR ((min Q •Λ (S º))º) º ⊆ min R •Λ (foldR S º)
greedy-theorem =
  begin
    foldR ((min Q •Λ (S º))º) º
      ⊆⟨ proj₂ (foldR-α-lemma (foldR ((min Q •Λ (S º))º) º)) ⟩
    foldR α • foldR ((min Q •Λ (S º))º) º
      ⊆⟨ hylo-least D α ((min Q •Λ (S º))º) M M-prefix-point ⟩
    min R •Λ H
      ⊆⟨ min-monotonic ⊆-refl (foldR-α-lemma (foldR S º)) ⟩
    min R •Λ (foldR S º)
  □
  where open PreorderReasoning (⊆-Preorder X (μ D)) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

GreedySolutionOD : OrnDesc (Σ I X) proj₁ D
GreedySolutionOD = algOrn D ((min Q •Λ (S º))º)

GreedySolution : ∀ {i} → X i → Set
GreedySolution x = μ ⌊ GreedySolutionOD ⌋ (_ , x)

optimisation-proof : ∀ {i} (x : X i) (sol : GreedySolution x) → Λ (min R •Λ (foldR S º)) x (forget ⌈ GreedySolutionOD ⌉ sol)
optimisation-proof x sol =
  modus-ponens-⊆ greedy-theorem x (forget ⌈ GreedySolutionOD ⌉ sol)
    (proj₂ (Iso.to Fun (Refinement.i (FRefinement.comp (toFRefinement (algOrn-FSwap D ((min Q •Λ (S º))º))) (ok (_ , x)))) sol))