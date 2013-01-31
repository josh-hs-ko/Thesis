-- Definition and properties of componentwise join.

module Thesis.Relation.Join where

open import Thesis.Relation

open import Function using (_∘_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------
-- componentwise join

⋃ : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) (R : X ↝⁺ (Y ∘ e)) → Σ I X ↝ Σ J Y
⋃ e (wrap R) (i , x) = map℘ (_,_ (e i)) (R i x)

⋃-monotonic : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) {R S : X ↝⁺ (Y ∘ e)} → R ⊆⁺ S → ⋃ {Y = Y} e R ⊆ ⋃ e S
⋃-monotonic e R⊆⁺S = wrap λ { (i , x) ._ (y , r , refl) → y , modus-ponens-⊆⁺ R⊆⁺S i x y r , refl }

⋃-cancellation : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) {R S : X ↝⁺ (Y ∘ e)} → ⋃ {Y = Y} e R ⊆ ⋃ e S → R ⊆⁺ S
⋃-cancellation {I} {J} {X} {Y} e {R} {S} ⋃R⊆⋃S = wrap λ i → wrap (aux i)
  where aux : (i : I) (x : X i) (y : Y (e i)) → (R !!) i x y → (S !!) i x y
        aux i x y r with modus-ponens-⊆ ⋃R⊆⋃S (i , x) (e i , y) (y , r , refl)
        aux i x y r | .y , s , refl = s

infix 7 _//_

_//_ : {I J : Set} {X : I → Set} {Y : J → Set} (R : Σ I X ↝ Σ J Y) (e : I → J) → X ↝⁺ (Y ∘ e)
R // e = wrap λ i x y → R (i , x) (e i , y)

//-monotonic : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) {R S : Σ I X ↝ Σ J Y} → R ⊆ S → R // e ⊆⁺ S // e
//-monotonic e R⊆S = wrap λ i → wrap λ x y r → modus-ponens-⊆ R⊆S (i , x) (e i , y) r

⋃-universal-⇒ : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) (R : X ↝⁺ (Y ∘ e)) (S : Σ I X ↝ Σ J Y) → ⋃ e R ⊆ S → R ⊆⁺ S // e
⋃-universal-⇒ e R S (wrap ⋃R⊆S) = wrap λ i → wrap λ x y r → ⋃R⊆S (i , x) (e i , y) (y , r , refl)

⋃-universal-⇐ : {I J : Set} {X : I → Set} {Y : J → Set} (e : I → J) (R : X ↝⁺ (Y ∘ e)) (S : Σ I X ↝ Σ J Y) → R ⊆⁺ S // e → ⋃ e R ⊆ S
⋃-universal-⇐ e R S R⊆⁺S// = wrap λ { (i , x) ._ (y , r , refl) → modus-ponens-⊆⁺ R⊆⁺S// i x y r }
