open import Thesis.Description
open import Thesis.Relation

module Thesis.Relation.Hylomorphism {I : Set} (D : Desc I) {X Y : I → Set} (R : Ḟ D Y ↝ Y) (S : Ḟ D X ↝ X) where

open import Thesis.Prelude.Implication
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Description
open import Thesis.Relation.Division
open import Thesis.Relation.Fold

open import Function using (_∘_; flip)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


hylo : X ↝ Y
hylo = foldR {D = D} R • foldR S º

hylo-fixed-point : hylo ≃ R • Ṙ D hylo • S º
hylo-fixed-point =
  begin
    foldR R • foldR S º
      ≃⟨ •-cong-l (foldR R) (º-cong (foldR-computation' D S)) ⟩
    foldR R • (S • Ṙ D (foldR S) • α º) º
      ≃⟨ Setoid.sym setoid (•-cong-l (foldR R) (º-cong (•-assoc S (Ṙ D (foldR S)) (α º)))) ⟩
    foldR R • ((S • Ṙ D (foldR S)) • α º) º
      ≃⟨ •-cong-l (foldR R) (º-preserves-comp (S • Ṙ D (foldR S)) (α º)) ⟩
    foldR R • α • (S • Ṙ D (foldR S)) º
      ≃⟨ Setoid.sym setoid (•-assoc (foldR R) α ((S • Ṙ D (foldR S)) º)) ⟩
    (foldR {D = D} R • α) • (S • Ṙ D (foldR S)) º
      ≃⟨ •-cong-r ((S • Ṙ D (foldR S)) º) (foldR-computation D R) ⟩
    (R • Ṙ D (foldR R)) • (S • Ṙ D (foldR S)) º
      ≃⟨ •-cong-l (R • Ṙ D (foldR R)) (º-preserves-comp S (Ṙ D (foldR S))) ⟩
    (R • Ṙ D (foldR R)) • Ṙ D (foldR S) º • S º
      ≃⟨ •-assoc R (Ṙ D (foldR R)) (Ṙ D (foldR S) º • S º) ⟩
    R • Ṙ D (foldR R) • Ṙ D (foldR S) º • S º
      ≃⟨ Setoid.sym setoid (•-cong-l R (•-assoc (Ṙ D (foldR R)) (Ṙ D (foldR S) º) (S º))) ⟩
    R • (Ṙ D (foldR R) • Ṙ D (foldR S) º) • S º
      ≃⟨ Setoid.sym setoid (•-cong-l R (•-cong-r (S º) (•-cong-l (Ṙ D (foldR R)) (Ṙ-preserves-conv D (foldR S)))))  ⟩
    R • (Ṙ D (foldR R) • Ṙ D (foldR S º)) • S º
      ≃⟨ Setoid.sym setoid (•-cong-l R (•-cong-r (S º) (Ṙ-preserves-comp D (foldR R) (foldR S º)))) ⟩
    R • Ṙ D (foldR R • foldR S º) • S º
  □
  where setoid = ≃-Setoid X Y
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

hylo-least : (T : X ↝ Y) → R • Ṙ D T • S º ⊆ T → hylo ⊆ T
hylo-least T =
  begin
    hylo ⊆ T
      ≈⟨ refl ⟩
    foldR R • foldR S º ⊆ T
      ⇐⟨ /-universal-⇒ ⟩
    foldR R ⊆ T / (foldR S º)
      ⇐⟨ foldR-least D R (T / (foldR S º)) ⟩
    R • Ṙ D (T / (foldR S º)) • α º ⊆ T / (foldR S º)
      ⇐⟨ /-universal-⇐ ⟩
    (R • Ṙ D (T / (foldR S º)) • α º) • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (proj₁ (•-assoc R (Ṙ D (T / (foldR S º)) • α º) (foldR S º))) ⟩
    R • (Ṙ D (T / (foldR S º)) • α º) • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (proj₁ (•-assoc (Ṙ D (T / (foldR S º))) (α º) (foldR S º)))) ⟩
    R • Ṙ D (T / (foldR S º)) • α º • foldR {D = D} S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (proj₂ (º-preserves-comp (foldR {D = D} S) α)))) ⟩
    R • Ṙ D (T / (foldR S º)) • (foldR {D = D} S • α) º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (º-monotonic (proj₁ (foldR-computation D S))))) ⟩
    R • Ṙ D (T / (foldR S º)) • (S • Ṙ D (foldR S)) º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (proj₁ (º-preserves-comp S (Ṙ D (foldR S)))))) ⟩
    R • Ṙ D (T / (foldR S º)) • Ṙ D (foldR S) º • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (•-monotonic-r (S º) (proj₂ (Ṙ-preserves-conv D (foldR S)))))) ⟩
    R • Ṙ D (T / (foldR S º)) • Ṙ D (foldR S º) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (proj₂ (•-assoc (Ṙ D (T / (foldR {D = D} S º))) (Ṙ D (foldR S º)) (S º)))) ⟩
    R • (Ṙ D (T / (foldR S º)) • Ṙ D (foldR S º)) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-r (S º) (proj₂ (Ṙ-preserves-comp D (T / (foldR S º)) (foldR S º))))) ⟩
    R • Ṙ D (T / (foldR S º) • foldR S º) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-r (S º) (Ṙ-monotonic D (/-universal-⇒ ⊆-refl)))) ⟩
    R • Ṙ D T • S º ⊆ T
  □
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)