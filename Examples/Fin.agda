-- Finite numbers, i.e., natural numbers bounded above by a given natural number.

module Examples.Fin where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament
open import Examples.Nat

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Data.List using (List; []; _∷_)

FinOD : OrnDesc Nat ! NatD
FinOD = wrap λ { (ok zero   ) → Δ ⊥ λ ()
               ; (ok (suc n)) → σ ListTag λ { `nil  → ṿ tt
                                            ; `cons → ṿ (ok n , tt) } }

Fin : Nat → Set
Fin = μ ⌊ FinOD ⌋
