-- Decidable total ordering on natural numbers and minimum.

module Examples.Nat.TotalOrdering where

open import Description
open import Ornament
open import Examples.Nat

open import Function using (_∘_; _∋_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym; trans)


--------
-- canonical less-than-or-equal-to ordering on natural numbers (bottom-up representation)

LeD : Desc (Nat × Nat)
LeD = wrap λ { (x , y) →
               σ ListTag λ { `nil  → σ[ _ ∈ x ≡ zero ] ṿ []
                           ; `cons → σ[ x' ∈ Nat ] σ[ y' ∈ Nat ] σ[ _ ∈ (suc x' , suc y') ≡ (Nat × Nat ∋ x , y) ] ṿ ((x' , y') ∷ []) } }

_≤_ : Nat → Nat → Set
x ≤ y = μ LeD (x , y)

_≰_ : Nat → Nat → Set
x ≰ y = ¬ (x ≤ y)

infix 3 _≤_ _≰_

≤-base : {y : Nat} → zero ≤ y
≤-base = con (`nil , refl , tt)

≤-step : {x y : Nat} → x ≤ y → suc x ≤ suc y
≤-step le = con (`cons , _ , _ , refl , le , tt)

≤-squeeze : {x : Nat} → x ≤ zero → x ≡ zero
≤-squeeze (con (`nil  , refl , _)) = refl
≤-squeeze (con (`cons , _ , _ , () , _))

≤-step⁻¹ : {x y : Nat} → suc x ≤ suc y → x ≤ y
≤-step⁻¹ (con (`nil  , () , _))
≤-step⁻¹ (con (`cons , _ , _ , refl , le , _)) = le

≤-refl : {x : Nat} → x ≤ x
≤-refl {con (`nil  ,     _)} = ≤-base
≤-refl {con (`cons , x , _)} = ≤-step (≤-refl {x})

≤-trans : {x y z : Nat} → x ≤ y → y ≤ z → x ≤ z
≤-trans (con (`nil , refl , _)) y≤z = ≤-base
≤-trans (con (`cons , _ , _ , refl , x≤y , _)) (con (`nil , () , _))
≤-trans (con (`cons , _ , _ , refl , x≤y , _)) (con (`cons , ._ , _ , refl , y≤z , _)) = ≤-step (≤-trans x≤y y≤z)

≰-invert : {x y : Nat} → x ≰ y → y ≤ x
≰-invert {x}                   {con (`nil  ,     _)} nle = ≤-base
≰-invert {con (`nil  ,     _)} {con (`cons , y , _)} nle = ⊥-elim (nle ≤-base)
≰-invert {con (`cons , x , _)} {con (`cons , y , _)} nle = ≤-step (≰-invert (nle ∘ ≤-step))

mutual

  _≤?_ : (x y : Nat) → Dec (x ≤ y)
  con (`nil  ,     _) ≤? y                   = yes ≤-base
  con (`cons , x , _) ≤? con (`nil  ,     _) = no (suc≢zero ∘ ≤-squeeze)
  con (`cons , x , _) ≤? con (`cons , y , _) = ≤?-with x y (x ≤? y)

  -- avoiding with-matching to circumvent a possible error of Agda

  ≤?-with : (x y : Nat) → Dec (x ≤ y) → Dec (suc x ≤ suc y)
  ≤?-with x y (yes x≤y) = yes (≤-step x≤y)
  ≤?-with x y (no  x≰y) = no (x≰y ∘ ≤-step⁻¹)
