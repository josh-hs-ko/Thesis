-- Sorted lists indexed by a lower bound as an ornamentation of lists.

module Examples.List.Sorted (Val : Set) (_≤_ : Val → Val → Set) (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z) where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Ornament
open import Ornament.RefinementSemantics
open import Examples.List

open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; _,_; proj₁; proj₂)


SListOD : OrnDesc Val ! ⌊ ListOD Val ⌋
SListOD = wrap λ { (ok b) → σ Bool λ { false → ∎
                                     ; true  → σ[ x ∶ Val ] Δ[ _ ∶ b ≤ x ] ṿ (ok x) } }

SList : Val → Set
SList = μ ⌊ SListOD ⌋

snil : ∀ {b} → SList b
snil = con (false , tt)

scons : (x : Val) → ∀ {b} → b ≤ x → SList x → SList b
scons x b≤x xs = con (true , x , b≤x , xs)

Sorted : Val → List Val → Set
Sorted b xs = OptP ⌈ SListOD ⌉ (ok b) xs

sorted-nil : ∀ {b} → Sorted b []
sorted-nil = con tt

sorted-cons : ∀ x → ∀ {b} → b ≤ x → ∀ {xs} → Sorted x xs → Sorted b (x ∷ xs)
sorted-cons x le s = con (le , s)

sorted-relax : ∀ {b b'} → b' ≤ b → ∀ {xs} → Sorted b xs → Sorted b' xs
sorted-relax b'≤b {xs = con (false , _)}      s               = sorted-nil
sorted-relax b'≤b {xs = con (true  , x , xs)} (con (b≤x , s)) = sorted-cons x (≤-trans b'≤b b≤x) s
