-- Ordered lists indexed with a lower bound as an ornamentation of lists.

module Examples.List.Ordered (Val : Set) (_≤_ : Val → Val → Set) where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament hiding ([]; _∷_)
open import Ornament.RefinementSemantics
open import Examples.Nat
open import Examples.List

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)


OrdListOD : OrnDesc Val ! ⌊ ListOD Val ⌋
OrdListOD = wrap λ { (ok b) → σ ListTag λ { `nil  → ṿ tt
                                          ; `cons → σ[ x ∈ Val ] Δ[ _ ∈ b ≤ x ] ṿ (ok x , tt) } }

OrdList : Val → Set
OrdList = μ ⌊ OrdListOD ⌋

onil : ∀ {b} → OrdList b
onil = con (`nil , tt)

ocons : (x : Val) {b : Val} → b ≤ x → OrdList x → OrdList b
ocons x b≤x xs = con (`cons , x , b≤x , xs , tt)

Ordered : Val → List Val → Set
Ordered b xs = OptP ⌈ OrdListOD ⌉ (ok b) xs

ordered-nil : {b : Val} → Ordered b []
ordered-nil = con tt

ordered-cons : (x : Val) {b : Val} → b ≤ x → {xs : List Val} → Ordered x xs → Ordered b (x ∷ xs)
ordered-cons x le s = con (le , s , tt)

ordered-relax : (≤-trans : {x y z : Val} → x ≤ y → y ≤ z → x ≤ z) →
                {b b' : Val} → b' ≤ b → {xs : List Val} → Ordered b xs → Ordered b' xs
ordered-relax ≤-trans b'≤b {xs = con (`nil  ,          _)} s                   = ordered-nil
ordered-relax ≤-trans b'≤b {xs = con (`cons , x , xs , _)} (con (b≤x , s , _)) = ordered-cons x (≤-trans b'≤b b≤x) s
