module Thesis.Examples.Nat where

open import Thesis.Description

open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; sym; trans)


--------
-- natural numbers

NatD : Desc ⊤
NatD = wrap λ _ → σ Bool λ { false → ∎
                           ; true  → ṿ tt }

Nat : Set
Nat = μ NatD tt

zero : Nat
zero = con (false , tt)

suc : Nat → Nat
suc n = con (true , n)

suc≢zero : ∀ {n} → suc n ≢ zero
suc≢zero ()

_+_ : Nat → Nat → Nat
con (false , _) + y = y
con (true  , x) + y = suc (x + y)

rhs-zero : ∀ x → x + zero ≡ x
rhs-zero (con (false , _)) = refl
rhs-zero (con (true  , x)) = cong suc (rhs-zero x)

rhs-suc : ∀ x y → x + suc y ≡ suc (x + y)
rhs-suc (con (false , _)) y = refl
rhs-suc (con (true  , x)) y = cong suc (rhs-suc x y)

comm : ∀ x y → x + y ≡ y + x
comm (con (false , _)) y = sym (rhs-zero y)
comm (con (true  , x)) y = trans (cong suc (comm x y)) (sym (rhs-suc y x))

assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
assoc (con (false , _)) y z = refl
assoc (con (true  , x)) y z = cong suc (assoc x y z)