-- This module defines the J rule for propositional equality, a generalised K rule for heterogeneous equality,
-- and a predicate specifying when an element of a setoid is the unique inhabitant of the setoid.

module Prelude.Equality where

open import Level
open import Data.Product using (Σ; _,_)
open import Relation.Binary using (Setoid; module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl)


--------
-- the J rule

elim-≡ : ∀ {a b} {A : Set a} {x : A} (P : {y : A} → x ≡ y → Set b) → P refl → {y : A} (eq : x ≡ y) → P eq
elim-≡ P p refl = p


--------
-- generalised uniqueness of identity proofs

proof-irrelevance' : ∀ {a} {A : Set a} {x x' y y' : A} → x ≡ x' → y ≡ y' → {eq : x ≡ y} {eq' : x' ≡ y'} → eq ≅ eq'
proof-irrelevance' refl refl {refl} {refl} = hrefl


--------
-- unique inhabitant

Unique : {ℓ₀ ℓ₁ : Level} (S : Setoid ℓ₀ ℓ₁) → Setoid.Carrier S → Set (ℓ₀ ⊔ ℓ₁)
Unique S x = (y : Carrier) → x ≈ y
  where open Setoid S

equal : {ℓ₀ ℓ₁ : Level} (S : Setoid ℓ₀ ℓ₁) → Σ[ x ∶ Setoid.Carrier S ] Unique S x → ∀ y z → Setoid._≈_ S y z
equal S (x , u) y z = trans (sym (u y)) (u z)
  where open Setoid S
