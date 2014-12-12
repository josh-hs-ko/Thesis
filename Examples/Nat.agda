-- Peano-style natural numbers.

module Examples.Nat where

open import Description

open import Function using (_∋_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym; trans)


--------
-- natural numbers

data ListTag : Set where
  `nil  : ListTag
  `cons : ListTag

NatD : Desc ⊤
NatD = wrap λ _ → σ ListTag λ { `nil   → ṿ []
                              ; `cons  → ṿ (tt ∷ []) }

Nat : Set
Nat = μ NatD tt

pattern zero  = con (`nil , tt)
pattern suc n = con (`cons , n , tt)

toℕ : Nat → ℕ
toℕ zero    = Data.Nat.zero
toℕ (suc n) = Data.Nat.suc (toℕ n)

suc≢zero : {n : Nat} → (Nat ∋ suc n) ≢ zero
suc≢zero ()

_+_ : Nat → Nat → Nat
zero  + y = y
suc x + y = suc (x + y)

rhs-zero : ∀ x → x + zero ≡ x
rhs-zero zero    = refl
rhs-zero (suc x) = cong suc (rhs-zero x)

rhs-suc : ∀ x y → x + suc y ≡ suc (x + y)
rhs-suc zero    y = refl
rhs-suc (suc x) y = cong suc (rhs-suc x y)

comm : ∀ x y → x + y ≡ y + x
comm zero    y = sym (rhs-zero y)
comm (suc x) y = trans (cong suc (comm x y)) (sym (rhs-suc y x))

assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
assoc zero    y z = refl
assoc (suc x) y z = cong suc (assoc x y z)
