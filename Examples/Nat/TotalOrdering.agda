module Thesis.Examples.Nat.TotalOrdering where

open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Examples.Nat

open import Function using (_∘_; type-signature)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; _,_; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym; trans)


--------
-- less-than-or-equal-to relation on natural numbers (bottom-up representation)

LeD : Desc (Nat × Nat)
LeD = wrap λ { (x , y) →
               σ Bool λ { false → σ[ _ ∶ x ≡ zero ] ∎
                        ; true  → σ[ x' ∶ Nat ] σ[ y' ∶ Nat ] σ[ _ ∶ (suc x' , suc y') ≡ (x , y ∶ Nat × Nat) ] ṿ (x' , y') } }

_≤_ : Nat → Nat → Set
x ≤ y = μ LeD (x , y)

_≰_ : Nat → Nat → Set
x ≰ y = ¬ (x ≤ y)

infix 3 _≤_ _≰_

≤-base : ∀ {y} → zero ≤ y
≤-base = con (false , refl , tt)

≤-step : ∀ {x y} → x ≤ y → suc x ≤ suc y
≤-step le = con (true , _ , _ , refl , le)

≤-squeeze : ∀ {x} → x ≤ zero → x ≡ zero
≤-squeeze (con (false , refl , _)) = refl
≤-squeeze (con (true , _ , _ , () , _))

≤-step⁻¹ : ∀ {x y} → suc x ≤ suc y → x ≤ y
≤-step⁻¹ (con (false , () , _))
≤-step⁻¹ (con (true , _ , _ , refl , le)) = le

≤-refl : ∀ {x} → x ≤ x
≤-refl {con (false , _)} = ≤-base
≤-refl {con (true  , x)} = ≤-step (≤-refl {x})

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans (con (false , refl , _)) y≤z = ≤-base
≤-trans (con (true , _ , _ , refl , x≤y)) (con (false , () , _))
≤-trans (con (true , _ , _ , refl , x≤y)) (con (true , ._ , _ , refl , y≤z)) = ≤-step (≤-trans x≤y y≤z)

≰-invert : ∀ {x y} → x ≰ y → y ≤ x
≰-invert {x}               {con (false , _)} nle = ≤-base
≰-invert {con (false , _)} {con (true  , y)} nle = ⊥-elim (nle ≤-base)
≰-invert {con (true  , x)} {con (true  , y)} nle = ≤-step (≰-invert (nle ∘ ≤-step))

mutual

  _≤?_ : (x y : Nat) → Dec (x ≤ y)
  con (false , _) ≤? y               = yes ≤-base
  con (true  , x) ≤? con (false , _) = no (suc≢zero ∘ ≤-squeeze)
  con (true  , x) ≤? con (true  , y) = ≤?-with x y (x ≤? y)

  -- avoiding with-matching to circumvent a likely bug of Agda

  ≤?-with : (x y : Nat) → Dec (x ≤ y) → Dec (suc x ≤ suc y)
  ≤?-with x y (yes x≤y) = yes (≤-step x≤y)
  ≤?-with x y (no  x≰y) = no (x≰y ∘ ≤-step⁻¹)

_⊓_ : Nat → Nat → Nat
con (false , _) ⊓ y               = zero
con (true  , x) ⊓ con (false , _) = zero
con (true  , x) ⊓ con (true  , y) = suc (x ⊓ y)

infixl 5 _⊓_

⊓-universal-⇒ : ∀ z x y →  z ≤ x ⊓ y  →  z ≤ x  ×  z ≤ y
⊓-universal-⇒ (con (false , _)) x                 y                 le                                   = ≤-base , ≤-base
⊓-universal-⇒ (con (true  , z)) (con (false , _)) y                 (con (false , () , _))
⊓-universal-⇒ (con (true  , z)) (con (false , _)) y                 (con (true  , _ , _ , () , _))
⊓-universal-⇒ (con (true  , z)) (con (true  , x)) (con (false , _)) (con (false , () , _))
⊓-universal-⇒ (con (true  , z)) (con (true  , x)) (con (false , _)) (con (true  , _ , _ , () , _))
⊓-universal-⇒ (con (true  , z)) (con (true  , x)) (con (true  , y)) (con (false  , () , _))
⊓-universal-⇒ (con (true  , z)) (con (true  , x)) (con (true  , y)) (con (true   , ._ , ._ , refl , le)) = (≤-step ** ≤-step)
                                                                                                             (⊓-universal-⇒ z x y le)

⊓-universal-⇐ : ∀ {z x y} →  z ≤ x  →  z ≤ y  →  z ≤ x ⊓ y
⊓-universal-⇐ (con (false , refl , _))           z≤y                                 = ≤-base
⊓-universal-⇐ (con (true  , _ , _ , refl , z≤x)) (con (false , () , _))
⊓-universal-⇐ (con (true  , _ , _ , refl , z≤x)) (con (true  , ._ , _ , refl , z≤y)) = ≤-step (⊓-universal-⇐ z≤x z≤y)
