open import Thesis.Description
open import Thesis.Relation

module Thesis.Relation.GreedyTheorem
  {I : Set} (D : Desc I) {X : I → Set} (R : μ D ↝ μ D) (S : Ḟ D X ↝ X)
  (R-transitive : R • R ⊆ R) (monotonicity : fun con • Ṙ D R • fun con º ⊆ R)
  (Q : Ḟ D X ↝ Ḟ D X) (greedy-condition : (fun con • Ṙ D (foldR S º)) • Q º ⊆ R º • (fun con • Ṙ D (foldR S º))) where

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
open import Relation.Binary using (Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning


H : X ↝ μ D
H = foldR {D = D} (fun con) • foldR S º

M : X ↝ μ D
M = min R •Λ H

first-obligation : fun con • Ṙ D M • min Q •Λ (S º) ⊆ H
first-obligation =
  begin
    fun con • Ṙ D (min R •Λ H) • min Q •Λ (S º)
      ⊆⟨ •-monotonic-l (fun con) (•-monotonic-r (min Q •Λ (S º)) (Ṙ-monotonic D (proj₁ (min-universal-⇒ ⊆-refl)))) ⟩
    fun con • Ṙ D H • min Q •Λ (S º)
      ⊆⟨ •-monotonic-l (fun con) (•-monotonic-l (Ṙ D H) (proj₁ (min-universal-⇒ ⊆-refl))) ⟩
    fun con • Ṙ D H • S º
      ⊆⟨ proj₂ (hylo-fixed-point D (fun con) S) ⟩
    H
  □
  where open PreorderReasoning (⊆-Preorder X (μ D)) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

second-obligation : (fun con • Ṙ D M • min Q •Λ (S º)) • H º ⊆ R
second-obligation =
  begin
    (fun con • Ṙ D M • min Q •Λ (S º)) • H º
      ⊆⟨ proj₁ (•-assoc (fun con) (Ṙ D M • min Q •Λ (S º)) (H º)) ⟩
    fun con • (Ṙ D M • min Q •Λ (S º)) • H º
      ⊆⟨ •-monotonic-l (fun con) (proj₁ (•-assoc (Ṙ D M) (min Q •Λ (S º)) (H º))) ⟩
    fun con • Ṙ D M • min Q •Λ (S º) • H º
      ⊆⟨ •-monotonic-l (fun con) (•-monotonic-r (min Q •Λ (S º) • H º) (Ṙ-monotonic D (min-monotonic ⊆-refl (foldR-con-lemma (foldR S º))))) ⟩
    fun con • Ṙ D (min R •Λ (foldR S º)) • min Q •Λ (S º) • H º
      ⊆⟨ proj₂ (•-assoc (fun con) (Ṙ D (min R •Λ (foldR S º))) (min Q •Λ (S º) • H º)) ⟩
    (fun con • Ṙ D (min R •Λ (foldR S º))) • min Q •Λ (S º) • H º
      ⊆⟨ •-monotonic-l (fun con • Ṙ D (min R •Λ (foldR S º)))
           (begin′
              min Q •Λ (S º) • H º
                ⊆⟨ proj₂ (º-preserves-comp H ((min Q •Λ (S º))º)) ⟩′
              (H • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-r ((min Q •Λ (S º))º) (proj₁ (hylo-fixed-point D (fun con) S))) ⟩′
              ((fun con • Ṙ D H • S º) • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-r (min Q •Λ (S º) º) (proj₂ (•-assoc (fun con) (Ṙ D H) (S º)))) ⟩′
              (((fun con • Ṙ D H) • S º) • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (proj₁ (•-assoc (fun con • Ṙ D H) (S º) ((min Q •Λ (S º))º))) ⟩′
              ((fun con • Ṙ D H) • S º • (min Q •Λ (S º))º) º
                ⊆⟨ º-monotonic (•-monotonic-l (fun con • Ṙ D H) (proj₂ (º-preserves-comp (min Q •Λ (S º)) S))) ⟩′
              ((fun con • Ṙ D H) • (min Q •Λ (S º) • S)º) º
                ⊆⟨ º-monotonic (•-monotonic-l (fun con • Ṙ D H) (º-monotonic (proj₂ (min-universal-⇒ ⊆-refl)))) ⟩′
              ((fun con • Ṙ D H) • Q º) º
                ⊆⟨ º-monotonic (•-monotonic-r (Q º) (•-monotonic-l (fun con) (Ṙ-monotonic D (proj₁ (foldR-con-lemma (foldR S º)))))) ⟩′
              ((fun con • Ṙ D (foldR S º)) • Q º) º
                ⊆⟨ º-monotonic greedy-condition ⟩′
              (R º • fun con • Ṙ D (foldR S º)) º
                ⊆⟨ proj₁ (º-preserves-comp (R º) (fun con • Ṙ D (foldR S º))) ⟩′
              (fun con • Ṙ D (foldR S º)) º • R
                ⊆⟨ •-monotonic-r R (proj₁ (º-preserves-comp (fun con) (Ṙ D (foldR S º)))) ⟩′
              ((Ṙ D (foldR S º)) º • fun con º) • R
                ⊆⟨ proj₁ (•-assoc (Ṙ D (foldR S º) º) (fun con º) R) ⟩′
              (Ṙ D (foldR S º)) º • fun con º • R
                ⊆⟨ •-monotonic-r (fun con º • R) (proj₂ (Ṙ-preserves-conv D (foldR S º))) ⟩′
              Ṙ D (foldR S) • fun con º • R
            □′) ⟩
    (fun con • Ṙ D (min R •Λ (foldR S º))) • Ṙ D (foldR S) • fun con º • R
      ⊆⟨ proj₂ (•-assoc (fun con • Ṙ D (min R •Λ (foldR S º))) (Ṙ D (foldR S)) (fun con º • R)) ⟩
    ((fun con • Ṙ D (min R •Λ (foldR S º))) • Ṙ D (foldR S)) • fun con º • R
      ⊆⟨ •-monotonic-r (fun con º • R) (proj₁ (•-assoc (fun con) (Ṙ D (min R •Λ (foldR S º))) (Ṙ D (foldR S)))) ⟩
    (fun con • Ṙ D (min R •Λ (foldR S º)) • Ṙ D (foldR S)) • fun con º • R
      ⊆⟨ •-monotonic-r (fun con º • R) (•-monotonic-l (fun con) (proj₂ (Ṙ-preserves-comp D (min R •Λ (foldR S º)) (foldR S)))) ⟩
    (fun con • Ṙ D (min R •Λ (foldR S º) • foldR S)) • fun con º • R
      ⊆⟨ •-monotonic-r (fun con º • R) (•-monotonic-l (fun con) (Ṙ-monotonic D (proj₂ (min-universal-⇒ ⊆-refl)))) ⟩
    (fun con • Ṙ D R) • fun con º • R
      ⊆⟨ proj₂ (•-assoc (fun con • Ṙ D R) (fun con º) R) ⟩
    ((fun con • Ṙ D R) • fun con º) • R
      ⊆⟨ •-monotonic-r R (proj₁ (•-assoc (fun con) (Ṙ D R) (fun con º))) ⟩
    (fun con • Ṙ D R • fun con º) • R
      ⊆⟨ •-monotonic-r R monotonicity ⟩
    R • R
      ⊆⟨ R-transitive ⟩
    R
  □
  where open PreorderReasoning (⊆-Preorder (μ D) (μ D))   renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)
        open PreorderReasoning (⊆-Preorder (μ D) (Ḟ D X)) renaming (begin_ to begin′_; _∼⟨_⟩_ to _⊆⟨_⟩′_; _∎ to _□′)

M-prefix-point : fun con • Ṙ D M • min Q •Λ (S º) ⊆ M
M-prefix-point = min-universal-⇐ first-obligation second-obligation

greedy-theorem : foldR ((min Q •Λ (S º))º) º ⊆ min R •Λ (foldR S º)
greedy-theorem =
  begin
    foldR ((min Q •Λ (S º))º) º
      ⊆⟨ proj₂ (foldR-con-lemma (foldR ((min Q •Λ (S º))º) º)) ⟩
    foldR (fun con) • foldR ((min Q •Λ (S º))º) º
      ⊆⟨ hylo-least D (fun con) ((min Q •Λ (S º))º) M M-prefix-point ⟩
    min R •Λ H
      ⊆⟨ min-monotonic ⊆-refl (foldR-con-lemma (foldR S º)) ⟩
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