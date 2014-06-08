-- Definition and properties of binary join and its componentwise version, and definition of summing join (kept for future work).

module Relation.Join where

open import Prelude.Preorder
open import Relation

open import Function using (id; _∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


_∪⁻_ : {X Y : Set} → X ↝⁻ Y → X ↝⁻ Y → X ↝⁻ Y
(R ∪⁻ S) x y = R x y ⊎ S x y

∪⁻-universal-⇒ : {X Y : Set} {R S T : X ↝⁻ Y} → R ∪⁻ S ⊆⁻ T → (R ⊆⁻ T) × (S ⊆⁻ T)
∪⁻-universal-⇒ R∪⁻S⊆⁻T = wrap (λ x y r → modus-ponens-⊆⁻ R∪⁻S⊆⁻T x y (inj₁ r)) ,
                      wrap (λ x y s → modus-ponens-⊆⁻ R∪⁻S⊆⁻T x y (inj₂ s))

∪⁻-universal-⇐ : {X Y : Set} {R S T : X ↝⁻ Y} → R ⊆⁻ T → S ⊆⁻ T → R ∪⁻ S ⊆⁻ T
∪⁻-universal-⇐ R⊆⁻T S⊆⁻T = wrap λ { x y (inj₁ r) → modus-ponens-⊆⁻ R⊆⁻T x y r
                               ; x y (inj₂ s) → modus-ponens-⊆⁻ S⊆⁻T x y s }

_∪_ : {I : Set} {X Y : I → Set} → X ↝ Y → X ↝ Y → X ↝ Y
(R ∪ S) = wrap λ i → (R !!) i ∪⁻ (S !!) i

∪-universal-⇒ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ∪ S ⊆ T → (R ⊆ T) × (S ⊆ T)
∪-universal-⇒ (wrap R∪S⊆T) = wrap (λ i → proj₁ (∪⁻-universal-⇒ (R∪S⊆T i))) , wrap (λ i → proj₂ (∪⁻-universal-⇒ (R∪S⊆T i)))

∪-universal-⇐ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ T → S ⊆ T → R ∪ S ⊆ T
∪-universal-⇐ (wrap R⊆T) (wrap S⊆T) = wrap λ i → ∪⁻-universal-⇐ (R⊆T i) (S⊆T i)


--------
-- summing join

⋃ : {I : Set} {X Y : I → Set} → X ↝ Y → Σ I X ↝⁻ Σ I Y
⋃ R (i , x) = map℘ (_,_ i) ((R !!) i x)

⋃-monotonic : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → ⋃ R ⊆⁻ ⋃ S
⋃-monotonic R⊆S = wrap λ { (i , x) ._ (y , r , refl) → y , modus-ponens-⊆ R⊆S i x y r , refl }

⋃-preserves-comp : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → ⋃ (R • S) ≃⁻ ⋃ R •⁻ ⋃ S
⋃-preserves-comp R S = wrap (λ { (i , x) ._ (z , (y , s , r) , refl) → (i , y) , (y , s , refl) , (z , r , refl) }) ,
                       wrap (λ { (i , x) ._ (._ , (y , s , refl) , (z , r , refl)) → z , (y , s , r) , refl })

⋃-cancellation : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → ⋃ R ⊆⁻ ⋃ S → R ⊆ S
⋃-cancellation {I} {X} {Y} {R} {S} ⋃R⊆⁻⋃S = wrap λ i → wrap (aux i)
  where aux : (i : I) (x : X i) (y : Y i) → (R !!) i x y → (S !!) i x y
        aux i x y r with modus-ponens-⊆⁻ ⋃R⊆⁻⋃S (i , x) (i , y) (y , r , refl)
        aux i x y r | .y , s , refl = s

infix 7 _/⁻/⁻

_/⁻/⁻ : {I : Set} {X Y : I → Set} (R : Σ I X ↝⁻ Σ I Y) → X ↝ Y
R /⁻/⁻ = wrap λ i x y → R (i , x) (i , y)

/⁻/⁻-monotonic : {I : Set} {X Y : I → Set} {R S : Σ I X ↝⁻ Σ I Y} → R ⊆⁻ S → R /⁻/⁻ ⊆ S /⁻/⁻
/⁻/⁻-monotonic R⊆⁻S = wrap λ i → wrap λ x y r → modus-ponens-⊆⁻ R⊆⁻S (i , x) (i , y) r

/⁻/⁻-preserves-comp' : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : Σ I X ↝⁻ Σ I Y) → (⋃ R •⁻ S) /⁻/⁻ ≃ R • S /⁻/⁻
/⁻/⁻-preserves-comp' R S = wrap (λ i → wrap λ { x .z ((.i , y) , s , (z , r , refl)) → y , s , r }) ,
                         wrap (λ i → wrap λ { x z (y , s , r) → (i , y) , (s , z , r , refl) })

⋃-universal-⇒ : {I : Set} {X Y : I → Set} (R : X ↝ Y) (S : Σ I X ↝⁻ Σ I Y) → ⋃ R ⊆⁻ S → R ⊆ S /⁻/⁻
⋃-universal-⇒ R S (wrap ⋃R⊆⁻S) = wrap λ i → wrap λ x y r → ⋃R⊆⁻S (i , x) (i , y) (y , r , refl)

⋃-universal-⇐ : {I : Set} {X Y : I → Set} (R : X ↝ Y) (S : Σ I X ↝⁻ Σ I Y) → R ⊆ S /⁻/⁻ → ⋃ R ⊆⁻ S
⋃-universal-⇐ R S R⊆S/⁻/⁻ = wrap λ { (i , x) ._ (y , r , refl) → modus-ponens-⊆ R⊆S/⁻/⁻ i x y r }

/⁻/⁻-⋃-inverse : {I : Set} {X Y : I → Set} (R : X ↝ Y) → (⋃ R) /⁻/⁻ ≃ R
/⁻/⁻-⋃-inverse R =
  (begin
     (⋃ R) /⁻/⁻ ⊆ R
       ⇐⟨ ⋃-cancellation ⟩
     ⋃ ((⋃ R) /⁻/⁻) ⊆⁻ ⋃ R
       ⇐⟨ ⋃-universal-⇐ ((⋃ R) /⁻/⁻) (⋃ R) ⟩
     (⋃ R) /⁻/⁻ ⊆ (⋃ R) /⁻/⁻
   □) ⊆-refl ,
  ⋃-universal-⇒ R (⋃ R) ⊆⁻-refl
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)

ω : {I J : Set} (X : J → Set) (e : I → J) → Σ I (X ∘ e) → Σ J X
ω X e (i , x) = (e i , x)

ωº⁻-ω-/⁻/⁻-lemma : {I J : Set} (X : J → Set) (e : I → J) → (fun⁻ (ω X e) º⁻ •⁻ fun⁻ (ω X e)) /⁻/⁻ ≃ idR
ωº⁻-ω-/⁻/⁻-lemma X e = wrap (λ i → wrap λ { x .x (._ , refl , refl) → refl }) , wrap (λ i → wrap λ { x .x refl → (e i , x) , refl , refl })
