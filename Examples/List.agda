-- Cons-lists as an ornamentation of natural numbers.

module Examples.List where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament
open import Examples.Nat

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)


--------
-- lists

ListOD : Set → OrnDesc ⊤ ! NatD
ListOD A = wrap λ _ → σ LTag λ { `nil  → ∎
                               ; `cons → Δ[ _ ∶ A ] ṿ (ok tt) }

List : Set → Set
List A = μ ⌊ ListOD A ⌋ tt

[] : ∀ {A} → List A
[] = con (`nil , tt)

_∷_ : ∀ {A} → A → List A → List A
x ∷ xs = con (`cons , x , xs)

infixr 5 _∷_

length : ∀ {A} → List A → Nat
length {A} = forget ⌈ ListOD A ⌉

_++_ : ∀ {A} → List A → List A → List A
con (`nil  , _) ++ ys      = ys
con (`cons , x , xs) ++ ys = x ∷ (xs ++ ys)
