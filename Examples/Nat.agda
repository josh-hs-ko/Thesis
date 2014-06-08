-- Peano-style natural numbers.

module Examples.Nat where

open import Description

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

zero : Nat
zero = con (`nil , tt)

suc : Nat → Nat
suc n = con (`cons , n , tt)

toℕ : Nat → ℕ
toℕ (con (`nil  ,     _)) = Data.Nat.zero
toℕ (con (`cons , n , _)) = Data.Nat.suc (toℕ n)

suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero ()

_+_ : Nat → Nat → Nat
con (`nil  ,     _) + y = y
con (`cons , x , _) + y = suc (x + y)

rhs-zero : ∀ x → x + zero ≡ x
rhs-zero (con (`nil  ,     _)) = refl
rhs-zero (con (`cons , x , _)) = cong suc (rhs-zero x)

rhs-suc : ∀ x y → x + suc y ≡ suc (x + y)
rhs-suc (con (`nil  ,     _)) y = refl
rhs-suc (con (`cons , x , _)) y = cong suc (rhs-suc x y)

comm : ∀ x y → x + y ≡ y + x
comm (con (`nil  ,     _)) y = sym (rhs-zero y)
comm (con (`cons , x , _)) y = trans (cong suc (comm x y)) (sym (rhs-suc y x))

assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
assoc (con (`nil  ,     _)) y z = refl
assoc (con (`cons , x , _)) y z = cong suc (assoc x y z)
