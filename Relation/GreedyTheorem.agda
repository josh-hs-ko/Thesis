-- A variant of the Greedy Theorem and its embedding into inductive families.

open import Description
open import Relation
open import Relation.Fold
open import Relation.Meet

module Relation.GreedyTheorem
  {I : Set} (D : Desc I) {X : I → Set} (R : μ D ↝ μ D) (S : Ḟ D X ↝ X)
  (R-transitive : R • R ⊆ R) (monotonicity : α • Ṙ D R • α º ⊆ R)
  (Q : Ḟ D X ↝ Ḟ D X) (greedy-condition : α • Ṙ D (foldR S º) • (Q ∩ (S º • S)) º ⊆ R º • α • Ṙ D (foldR S º)) where

open import Prelude.InverseImage
open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Relation.Hylomorphism
open import Relation.Minimum
open import Ornament
open import Ornament.Algebraic
open import Refinement
open import Relation.CompChain

open import Function using (id)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning


private

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
        ⊆⟨ ⊆-chain-l (α ▪ Ṙ D H ◇) (proj₁ (min-universal-⇒ ⊆-refl)) ⟩
      α • Ṙ D H • S º
        ⊆⟨ proj₂ (hylo-fixed-point D α S) ⟩
      H
    □
    where open PreorderReasoning (⊆-Preorder X (μ D)) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

  second-obligation : (α • Ṙ D M • min Q •Λ (S º)) • H º ⊆ R
  second-obligation =
    begin
      (α • Ṙ D M • min Q •Λ (S º)) • H º
        ⊆⟨ proj₁ (chain-normalise (([ α ] ▪ [ Ṙ D M ] ▪ [ min Q •Λ (S º) ]) ▪ [ H º ])) ⟩
      α • Ṙ D M • min Q •Λ (S º) • H º
        ⊆⟨ •-monotonic-l α (•-monotonic-r (min Q •Λ (S º) • H º) (Ṙ-monotonic D (min-monotonic ⊆-refl (foldR-α-lemma (foldR S º))))) ⟩
      α • Ṙ D (min R •Λ (foldR S º)) • min Q •Λ (S º) • H º
        ⊆⟨ ⊆-chain-l (α ▪ Ṙ D (min R •Λ (foldR S º)) ◇)
             (begin′
                min Q •Λ (S º) • H º
                  ⊆⟨ proj₂ (º-preserves-comp H ((min Q •Λ (S º))º)) ⟩′
                (H • (min Q •Λ (S º))º) º
                  ⊆⟨ º-monotonic (⊆-chain-r (H ◇) (α ▪ Ṙ D H ▪ (S º) ◇) (proj₁ (hylo-fixed-point D α S))) ⟩′
                (α • Ṙ D H • S º • (min Q •Λ (S º))º) º
                  ⊆⟨ º-monotonic (⊆-chain-l (α ▪ Ṙ D H ◇) (proj₂ (º-preserves-comp (min Q •Λ (S º)) S))) ⟩′
                (α • Ṙ D H • (min Q •Λ (S º) • S)º) º
                  ⊆⟨ º-monotonic (⊆-chain-l (α ▪ Ṙ D H ◇) (º-monotonic (•-monotonic-r S (proj₁ (min-context Q (S º)))))) ⟩′
                (α • Ṙ D H • (min (Q ∩ (S º • S)) •Λ (S º) • S)º) º
                  ⊆⟨ º-monotonic (⊆-chain-l (α ▪ Ṙ D H ◇) (º-monotonic (proj₂ (min-universal-⇒ ⊆-refl)))) ⟩′
                (α • Ṙ D H • (Q ∩ (S º • S)) º) º
                  ⊆⟨ º-monotonic (⊆-chain (α ◇) (Ṙ D H ◇) (Ṙ D (foldR S º) ◇) (Ṙ-monotonic D (proj₁ (foldR-α-lemma (foldR S º))))) ⟩′
                (α • Ṙ D (foldR S º) • (Q ∩ (S º • S)) º) º
                  ⊆⟨ º-monotonic greedy-condition ⟩′
                (R º • α • Ṙ D (foldR S º)) º
                  ⊆⟨ proj₁ (º-chain (R º ▪ α ▪ Ṙ D (foldR S º) ◇)) ⟩′
                Ṙ D (foldR S º) º • α º • R
                  ⊆⟨ ⊆-chain-r ((Ṙ D (foldR S º) º) ◇) (Ṙ D (foldR S) ◇) (proj₂ (Ṙ-preserves-conv D (foldR S º))) ⟩′
                Ṙ D (foldR S) • α º • R
              □′) ⟩
      α • Ṙ D (min R •Λ (foldR S º)) • Ṙ D (foldR S) • α º • R
        ⊆⟨ ⊆-chain (α ◇) (Ṙ D (min R •Λ (foldR S º)) ▪ Ṙ D (foldR S) ◇) (Ṙ D (min R •Λ (foldR S º) • foldR S) ◇)
             (proj₂ (Ṙ-preserves-comp D (min R •Λ (foldR S º)) (foldR S))) ⟩
      α • Ṙ D (min R •Λ (foldR S º) • foldR S) • α º • R
        ⊆⟨ ⊆-chain (α ◇) (Ṙ D (min R •Λ (foldR S º) • foldR S) ◇) (Ṙ D R ◇) (Ṙ-monotonic D (proj₂ (min-universal-⇒ ⊆-refl))) ⟩
      α • Ṙ D R • α º • R
        ⊆⟨ ⊆-chain-r (α ▪ Ṙ D R ▪ α º ◇) (R ◇) monotonicity ⟩
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

GreedySolution : (i : I) → X i → Set
GreedySolution i x = μ ⌊ GreedySolutionOD ⌋ (i , x)

optimisation-proof : (i : I) (x : X i) (sol : GreedySolution i x) → ((min R •Λ (foldR S º)) !!) i x (forget ⌈ GreedySolutionOD ⌉ sol)
optimisation-proof i x sol =
  modus-ponens-⊆ greedy-theorem i x (forget ⌈ GreedySolutionOD ⌉ sol)
    (proj₂ (Iso.to Fun (Refinement.i (FRefinement.comp (toFRefinement (algOrn-FSwap D ((min Q •Λ (S º))º))) (ok (_ , x)))) sol))
