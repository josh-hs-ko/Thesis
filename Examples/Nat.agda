-- Peano-style natural numbers.

module Examples.Nat where

open import Description

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym; trans)


--------
-- natural numbers

data LTag : Set where
  `nil  : LTag
  `cons : LTag

NatD : Desc ⊤
NatD = wrap λ _ → σ LTag λ { `nil  → ∎
                           ; `cons → ṿ tt }

Nat : Set
Nat = μ NatD tt

zero : Nat
zero = con (`nil , tt)

suc : Nat → Nat
suc n = con (`cons , n)

toℕ : Nat → ℕ
toℕ (con (`nil  , _)) = zeroℕ
toℕ (con (`cons , n)) = sucℕ (toℕ n)

suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero ()

_+_ : Nat → Nat → Nat
con (`nil  , _) + y = y
con (`cons , x) + y = suc (x + y)

rhs-zero : ∀ x → x + zero ≡ x
rhs-zero (con (`nil  , _)) = refl
rhs-zero (con (`cons , x)) = cong suc (rhs-zero x)

rhs-suc : ∀ x y → x + suc y ≡ suc (x + y)
rhs-suc (con (`nil  , _)) y = refl
rhs-suc (con (`cons , x)) y = cong suc (rhs-suc x y)

comm : ∀ x y → x + y ≡ y + x
comm (con (`nil  , _)) y = sym (rhs-zero y)
comm (con (`cons , x)) y = trans (cong suc (comm x y)) (sym (rhs-suc y x))

assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
assoc (con (`nil  , _)) y z = refl
assoc (con (`cons , x)) y z = cong suc (assoc x y z)
