-- This module defines the J rule for propositional equality, a generalised K rule for heterogeneous equality,
-- and a predicate specifying when an element of a setoid is the unique inhabitant of the setoid.

module Prelude.Equality where

open import Level
open import Function using (_on_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_) renaming (map to _**_)
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

equal : {ℓ₀ ℓ₁ : Level} (S : Setoid ℓ₀ ℓ₁) → Σ[ x ∈ Setoid.Carrier S ] Unique S x → ∀ y z → Setoid._≈_ S y z
equal S (x , u) y z = trans (sym (u y)) (u z)
  where open Setoid S


--------
-- creation of a setoid relative to an existing one

toSetoid : {ℓ₀ ℓ₁ ℓ₂ : Level} (S : Setoid ℓ₀ ℓ₁) {X : Set ℓ₂} → (X → Setoid.Carrier S) → Setoid ℓ₂ ℓ₁
toSetoid S {X} f =
  record { Carrier = X
         ; _≈_     = Setoid._≈_ S on f
         ; isEquivalence = record { refl = Setoid.refl S; sym = Setoid.sym S; trans = Setoid.trans S } }


--------
-- 

ProductSetoid : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level} → Setoid ℓ₀ ℓ₁ → Setoid ℓ₂ ℓ₃ → Setoid (ℓ₀ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₃)
ProductSetoid S T =
  record { Carrier = Setoid.Carrier S × Setoid.Carrier T
         ; _≈_ = λ { (x , y) (x' , y') → Setoid._≈_ S x x' × Setoid._≈_ T y y' }
         ; isEquivalence =
             record { refl  = Setoid.refl S , Setoid.refl T
                    ; sym   = Setoid.sym S ** Setoid.sym T
                    ; trans = λ { (eqS , eqT) (eqS' , eqT') → Setoid.trans S eqS eqS' , Setoid.trans T eqT eqT' } } }
