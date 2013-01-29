-- Cons-lists as an ornamentation of natural numbers.

module Thesis.Examples.List where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Examples.Nat

open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; _,_)


--------
-- lists

ListO : Set → OrnDesc ⊤ ! NatD
ListO A = wrap λ _ → σ Bool λ { false → ∎
                              ; true  → Δ[ _ ∶ A ] ṿ (ok tt) }

List : Set → Set
List A = μ ⌊ ListO A ⌋ tt

[] : ∀ {A} → List A
[] = con (false , tt)

_∷_ : ∀ {A} → A → List A → List A
x ∷ xs = con (true , x , xs)

infixr 5 _∷_

length : ∀ {A} → List A → Nat
length {A} = forget ⌈ ListO A ⌉

_++_ : ∀ {A} → List A → List A → List A
con (false , _) ++ ys      = ys
con (true  , x , xs) ++ ys = x ∷ (xs ++ ys)