-- Definition of hylomorphisms and the Hylomorphism Theorem.

open import Description
open import Relation

module Relation.Hylomorphism {I : Set} (D : Desc I) {X Y : I → Set} (R : Ḟ D Y ↝ Y) (S : Ḟ D X ↝ X) where

open import Prelude.Preorder
open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Description
open import Relation.CompChain
open import Relation.Division
open import Relation.Fold

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
      ≃⟨ •-cong-l (foldR R) (º-chain (S ▪ Ṙ D (foldR S) ▪ α º ◇)) ⟩
    foldR R • α • Ṙ D (foldR S) º • S º
      ≃⟨ Setoid.sym setoid (≃-chain (foldR R ▪ α ◇) (Ṙ D (foldR S º) ◇) (Ṙ D (foldR S) º ◇) (Ṙ-preserves-conv D (foldR S))) ⟩
    foldR R • α • Ṙ D (foldR S º) • S º
      ≃⟨ ≃-chain-r (foldR R ▪ α ◇) (R ▪ Ṙ D (foldR R) ◇) (foldR-computation D R) ⟩
    R • Ṙ D (foldR R) • Ṙ D (foldR S º) • S º
      ≃⟨ Setoid.sym setoid (≃-chain (R ◇) (Ṙ D (foldR R • foldR S º) ◇) (Ṙ D (foldR R) ▪ Ṙ D (foldR S º) ◇)
           (Ṙ-preserves-comp D (foldR R) (foldR S º))) ⟩
    R • Ṙ D (foldR R • foldR S º) • S º
  □
  where setoid = ≃-Setoid X Y
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

hylo-least : (T : X ↝ Y) → R • Ṙ D T • S º ⊆ T → hylo ⊆ T
hylo-least T =
  begin
    foldR R • foldR S º ⊆ T
      ⇐⟨ /-universal-⇒ ⟩
    foldR R ⊆ T / (foldR S º)
      ⇐⟨ foldR-least D R (T / (foldR S º)) ⟩
    R • Ṙ D (T / (foldR S º)) • α º ⊆ T / (foldR S º)
      ⇐⟨ /-universal-⇐ ⟩
    (R • Ṙ D (T / (foldR S º)) • α º) • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (proj₁ (chain-normalise (([ R ] ▪ [ Ṙ D (T / foldR S º) ] ▪ [ α º ]) ▪ [ foldR S º ]))) ⟩
    R • Ṙ D (T / (foldR S º)) • α º • foldR {D = D} S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R
           (begin′
              Ṙ D (T / (foldR S º)) • α º • foldR {D = D} S º
                ⊆⟨ •-monotonic-l (Ṙ D (T / (foldR S º))) (proj₂ (º-preserves-comp (foldR {D = D} S) α)) ⟩
              Ṙ D (T / (foldR S º)) • (foldR {D = D} S • α) º
                ⊆⟨ •-monotonic-l (Ṙ D (T / (foldR S º))) (º-monotonic (proj₁ (foldR-computation D S))) ⟩
              Ṙ D (T / (foldR S º)) • (S • Ṙ D (foldR S)) º
                ⊆⟨ •-monotonic-l (Ṙ D (T / (foldR S º))) (proj₁ (º-preserves-comp S (Ṙ D (foldR S)))) ⟩
              Ṙ D (T / (foldR S º)) • Ṙ D (foldR S) º • S º
                ⊆⟨ ⊆-chain (Ṙ D (T / (foldR S º)) ◇) (Ṙ D (foldR S) º ◇) (Ṙ D (foldR S º) ◇) (proj₂ (Ṙ-preserves-conv D (foldR S))) ⟩
              Ṙ D (T / (foldR S º)) • Ṙ D (foldR S º) • S º
                ⊆⟨ ⊆-chain-r (Ṙ D (T / (foldR S º)) ▪ Ṙ D (foldR S º) ◇) (Ṙ D ((T / (foldR S º)) • foldR S º) ◇)
                     (proj₂ (Ṙ-preserves-comp D (T / (foldR S º)) (foldR S º))) ⟩
              Ṙ D ((T / (foldR S º)) • foldR S º) • S º
                ⊆⟨ •-monotonic-r (S º) (Ṙ-monotonic D (/-universal-⇒ ⊆-refl)) ⟩
              Ṙ D T • S º
            □′)) ⟩
    R • Ṙ D T • S º ⊆ T
  □
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)
        open PreorderReasoning (⊆-Preorder X (Ḟ D Y)) renaming (begin_ to begin′_; _∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□′)
