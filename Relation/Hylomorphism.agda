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
open import Relation.Binary using (Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


hylo : X ↝ Y
hylo = foldR {D = D} R • foldR S º

hylo-fixed-point : hylo ≃ R • Ṙ D hylo • S º
hylo-fixed-point =
  begin
    hylo
      ≃⟨ Setoid.refl (≃-Setoid X Y) ⟩
    foldR {D = D} R • foldR S º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-cong-l (foldR R) (º-cong (idR-r (foldR S)))) ⟩
    foldR {D = D} R • (foldR S • idR) º
      ≃⟨ Setoid.sym (≃-Setoid X Y)
           (•-cong-l (foldR R) (º-cong (•-cong-l (foldR S) (fun-cong (λ {i} → Iso.from-to-inverse Fun (μ-iso D i)))))) ⟩
    foldR {D = D} R • (foldR {D = D} S • fun (con ∘ decon)) º
      ≃⟨ •-cong-l (foldR R) (º-cong (•-cong-l (foldR S) (fun-preserves-comp con decon))) ⟩
    foldR {D = D} R • (foldR {D = D} S • fun con • fun decon) º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-cong-l (foldR R) (º-cong (•-assoc (foldR S) (fun con) (fun decon)))) ⟩
    foldR {D = D} R • ((foldR {D = D} S • fun con) • fun decon) º
      ≃⟨ •-cong-l (foldR R) (º-cong (•-cong-r (fun decon) (foldR-computation D S))) ⟩
    foldR {D = D} R • ((S • Ṙ D (foldR S)) • fun decon) º
      ≃⟨ •-cong-l (foldR R) (º-preserves-comp (S • Ṙ D (foldR S)) (fun decon)) ⟩
    foldR {D = D} R • fun decon º • (S • Ṙ D (foldR S)) º
      ≃⟨ •-cong-l (foldR R) (•-cong-r ((S • Ṙ D (foldR S)) º) (iso-conv (μ-iso D))) ⟩
    foldR {D = D} R • fun con • (S • Ṙ D (foldR S)) º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-assoc (foldR R) (fun con) ((S • Ṙ D (foldR S)) º)) ⟩
    (foldR {D = D} R • fun con) • (S • Ṙ D (foldR S)) º
      ≃⟨ •-cong-r ((S • Ṙ D (foldR S)) º) (foldR-computation D R) ⟩
    (R • Ṙ D (foldR {D = D} R)) • (S • Ṙ D (foldR S)) º
      ≃⟨ •-cong-l (R • Ṙ D (foldR R)) (º-preserves-comp S (Ṙ D (foldR S))) ⟩
    (R • Ṙ D (foldR {D = D} R)) • Ṙ D (foldR S) º • S º
      ≃⟨ •-assoc R (Ṙ D (foldR R)) (Ṙ D (foldR S) º • S º) ⟩
    R • Ṙ D (foldR {D = D} R) • Ṙ D (foldR S) º • S º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-cong-l R (•-assoc (Ṙ D (foldR R)) (Ṙ D (foldR S) º) (S º))) ⟩
    R • (Ṙ D (foldR {D = D} R) • Ṙ D (foldR S) º) • S º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-cong-l R (•-cong-r (S º) (•-cong-l (Ṙ D (foldR R)) (Ṙ-preserves-conv D (foldR S)))))  ⟩
    R • (Ṙ D (foldR {D = D} R) • Ṙ D (foldR S º)) • S º
      ≃⟨ Setoid.sym (≃-Setoid X Y) (•-cong-l R (•-cong-r (S º) (Ṙ-preserves-comp D (foldR R) (foldR S º)))) ⟩
    R • (Ṙ D (foldR {D = D} R • foldR S º)) • S º
      ≃⟨ Setoid.refl (≃-Setoid X Y) ⟩
    R • Ṙ D hylo • S º
  □
  where open EqReasoning (≃-Setoid X Y) renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

hylo-least : (T : X ↝ Y) → R • Ṙ D T • S º ⊆ T → hylo ⊆ T
hylo-least T =
  begin
    hylo ⊆ T
      ≈⟨ refl ⟩
    foldR {D = D} R • foldR S º ⊆ T
      ⇐⟨ /-universal-⇒ ⟩
    foldR {D = D} R ⊆ T / (foldR S º)
      ⇐⟨ foldR-least D R (T / (foldR S º)) ⟩
    R • Ṙ D (T / (foldR S º)) • fun (con {D = D}) º ⊆ T / (foldR S º)
      ⇐⟨ /-universal-⇐ ⟩
    (R • Ṙ D (T / (foldR S º)) • fun (con {D = D}) º) • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (proj₁ (•-assoc R (Ṙ D (T / (foldR S º)) • fun con º) (foldR S º))) ⟩
    R • (Ṙ D (T / (foldR S º)) • fun (con {D = D}) º) • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (proj₁ (•-assoc (Ṙ D (T / (foldR S º))) (fun con º) (foldR S º)))) ⟩
    R • Ṙ D (T / (foldR S º)) • fun (con {D = D}) º • foldR S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (proj₂ (º-preserves-comp (foldR S) (fun (con {D = D})))))) ⟩
    R • Ṙ D (T / (foldR S º)) • (foldR S • fun (con {D = D})) º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (º-monotonic (proj₁ (foldR-computation D S))))) ⟩
    R • Ṙ D (T / (foldR {D = D} S º)) • (S • Ṙ D (foldR S)) º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (proj₁ (º-preserves-comp S (Ṙ D (foldR S)))))) ⟩
    R • Ṙ D (T / (foldR {D = D} S º)) • Ṙ D (foldR S) º • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-l (Ṙ D (T / (foldR S º))) (•-monotonic-r (S º) (proj₂ (Ṙ-preserves-conv D (foldR S)))))) ⟩
    R • Ṙ D (T / (foldR {D = D} S º)) • Ṙ D (foldR S º) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (proj₂ (•-assoc (Ṙ D (T / (foldR {D = D} S º))) (Ṙ D (foldR S º)) (S º)))) ⟩
    R • (Ṙ D (T / (foldR {D = D} S º)) • Ṙ D (foldR S º)) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-r (S º) (proj₂ (Ṙ-preserves-comp D (T / (foldR S º)) (foldR S º))))) ⟩
    R • Ṙ D (T / (foldR {D = D} S º) • foldR S º) • S º ⊆ T
      ⇐⟨ ⊆-trans (•-monotonic-l R (•-monotonic-r (S º) (Ṙ-monotonic D (/-universal-⇒ ⊆-refl)))) ⟩
    R • Ṙ D T • S º ⊆ T
  □
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)