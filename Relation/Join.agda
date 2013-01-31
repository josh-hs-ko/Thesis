-- Definition and properties of componentwise join.

module Thesis.Relation.Join where

open import Thesis.Prelude.Preorder
open import Thesis.Relation

open import Function using (id; _∘_)
open import Data.Product using (Σ; _,_; _×_)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


⋃ : {I : Set} {X Y : I → Set} → X ↝⁺ Y → Σ I X ↝ Σ I Y
⋃ R (i , x) = map℘ (_,_ i) ((R !!) i x)

⋃-preserves-comp : {I : Set} {X Y Z : I → Set} (R : Y ↝⁺ Z) (S : X ↝⁺ Y) → ⋃ (R •⁺ S) ≃ ⋃ R • ⋃ S
⋃-preserves-comp R S = wrap (λ { (i , x) ._ (z , (y , s , r) , refl) → (i , y) , (y , s , refl) , (z , r , refl) }) ,
                       wrap (λ { (i , x) ._ (._ , (y , s , refl) , (z , r , refl)) → z , (y , s , r) , refl })

⋃-monotonic : {I : Set} {X Y : I → Set} {R S : X ↝⁺ Y} → R ⊆⁺ S → ⋃ R ⊆ ⋃ S
⋃-monotonic R⊆⁺S = wrap λ { (i , x) ._ (y , r , refl) → y , modus-ponens-⊆⁺ R⊆⁺S i x y r , refl }

⋃-cancellation : {I : Set} {X Y : I → Set} {R S : X ↝⁺ Y} → ⋃ R ⊆ ⋃ S → R ⊆⁺ S
⋃-cancellation {I} {X} {Y} {R} {S} ⋃R⊆⋃S = wrap λ i → wrap (aux i)
  where aux : (i : I) (x : X i) (y : Y i) → (R !!) i x y → (S !!) i x y
        aux i x y r with modus-ponens-⊆ ⋃R⊆⋃S (i , x) (i , y) (y , r , refl)
        aux i x y r | .y , s , refl = s

infix 7 _//

_// : {I : Set} {X Y : I → Set} (R : Σ I X ↝ Σ I Y) → X ↝⁺ Y
R // = wrap λ i x y → R (i , x) (i , y)

//-monotonic : {I : Set} {X Y : I → Set} {R S : Σ I X ↝ Σ I Y} → R ⊆ S → R // ⊆⁺ S //
//-monotonic R⊆S = wrap λ i → wrap λ x y r → modus-ponens-⊆ R⊆S (i , x) (i , y) r

⋃-universal-⇒ : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) (S : Σ I X ↝ Σ I Y) → ⋃ R ⊆ S → R ⊆⁺ S //
⋃-universal-⇒ R S (wrap ⋃R⊆S) = wrap λ i → wrap λ x y r → ⋃R⊆S (i , x) (i , y) (y , r , refl)

⋃-universal-⇐ : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) (S : Σ I X ↝ Σ I Y) → R ⊆⁺ S // → ⋃ R ⊆ S
⋃-universal-⇐ R S R⊆⁺S// = wrap λ { (i , x) ._ (y , r , refl) → modus-ponens-⊆⁺ R⊆⁺S// i x y r }

//-⋃-inverse : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) → (⋃ R) // ≃⁺ R
//-⋃-inverse R =
  (begin
     (⋃ R) // ⊆⁺ R
       ⇐⟨ ⋃-cancellation ⟩
     ⋃ ((⋃ R) //) ⊆ ⋃ R
       ⇐⟨ ⋃-universal-⇐ ((⋃ R) //) (⋃ R) ⟩
     (⋃ R) // ⊆⁺ (⋃ R) //
   □) ⊆⁺-refl ,
  ⋃-universal-⇒ R (⋃ R) ⊆-refl
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)
