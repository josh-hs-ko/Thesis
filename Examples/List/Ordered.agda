-- Ordered lists indexed by a lower bound as an ornamentation of lists.

module Examples.List.Ordered (Val : Set) (_≤_ : Val → Val → Set) (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z) where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament
open import Ornament.RefinementSemantics
open import Examples.Nat
open import Examples.List

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)


OrdListOD : OrnDesc Val ! ⌊ ListOD Val ⌋
OrdListOD = wrap λ { (ok b) → σ LTag λ { `nil  → ∎
                                       ; `cons → σ[ x ∶ Val ] Δ[ _ ∶ b ≤ x ] ṿ (ok x) } }

OrdList : Val → Set
OrdList = μ ⌊ OrdListOD ⌋

onil : ∀ {b} → OrdList b
onil = con (`nil , tt)

ocons : (x : Val) → ∀ {b} → b ≤ x → OrdList x → OrdList b
ocons x b≤x xs = con (`cons , x , b≤x , xs)

Ordered : Val → List Val → Set
Ordered b xs = OptP ⌈ OrdListOD ⌉ (ok b) xs

ordered-nil : ∀ {b} → Ordered b []
ordered-nil = con tt

ordered-cons : ∀ x → ∀ {b} → b ≤ x → ∀ {xs} → Ordered x xs → Ordered b (x ∷ xs)
ordered-cons x le s = con (le , s)

ordered-relax : ∀ {b b'} → b' ≤ b → ∀ {xs} → Ordered b xs → Ordered b' xs
ordered-relax b'≤b {xs = con (`nil  , _)}      s               = ordered-nil
ordered-relax b'≤b {xs = con (`cons , x , xs)} (con (b≤x , s)) = ordered-cons x (≤-trans b'≤b b≤x) s
