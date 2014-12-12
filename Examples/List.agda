-- Cons-lists as an ornamentation of natural numbers.

module Examples.List where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament hiding ([]; _∷_)
open import Examples.Nat

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_)


--------
-- lists

ListOD : Set → OrnDesc ⊤ ! NatD
ListOD A = wrap λ _ → σ ListTag λ { `nil   → ṿ tt
                                  ; `cons  → Δ[ _ ∈ A ] ṿ (ok tt , tt) }

List : Set → Set
List A = μ ⌊ ListOD A ⌋ tt

pattern []       = con (`nil , tt)
pattern _∷_ x xs = con (`cons , x , xs , tt)

infixr 5 _∷_

length : {A : Set} → List A → Nat
length {A} = forget ⌈ ListOD A ⌉

_++_ : {A : Set} → List A → List A → List A
con (`nil  ,          _) ++ ys = ys
con (`cons , x , xs , _) ++ ys = x ∷ (xs ++ ys)
