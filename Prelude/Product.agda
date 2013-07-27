-- Auxiliary operations for dependent pairs.

module Prelude.Product where

open import Prelude.Function
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.Equality

open import Function using (_∘_; type-signature)
open import Data.Product using (Σ; _,_; _×_; curry) renaming (map to _**_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl)


cong₂-pair : {A : Set} {B : A → Set} → {a a' : A} {b : B a} {b' : B a'} → a ≡ a' → b ≅ b' → (a , b ∶ Σ A B) ≡ (a' , b')
cong₂-pair refl hrefl = refl

cong-proj₂ : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {y y' : B x} → (x , y ∶ Σ A B) ≡ (x , y') → y ≡ y'
cong-proj₂ refl = refl

Σ' : {A : Set} (B : A → Set) (C : Σ A B → Set) → A → Set
Σ' B C x = Σ (B x) (curry C x)

_×'_ : {A : Set} (B : A → Set) (C : A → Set) → A → Set
(B ×' C) x = B x × C x

Σ-assoc : {A : Set} (B : A → Set) (C : Σ A B → Set) → Iso (Σ (Σ A B) C) (Σ A (Σ' B C))
Σ-assoc B C =
  record { to   = λ { ((a , b) , c) → a , b , c }
         ; from = λ { (a , b , c) → (a , b) , c }
         ; to-from-inverse = λ { (a , b , c) → refl }
         ; from-to-inverse = λ { ((a , b) , c) → refl } }

prodIso : ∀ {A B C D} → Iso A B → Iso C D → Iso (A × C) (B × D)
prodIso ab cd =
  record { to   = to ab ** to cd
         ; from = from ab ** from cd
         ; to-from-inverse = λ _ → cong₂ _,_ (to-from-inverse ab _) (to-from-inverse cd _)
         ; from-to-inverse = λ _ → cong₂ _,_ (from-to-inverse ab _) (from-to-inverse cd _) }
  where open Iso

commIso : ∀ {A B} → Iso (A × B) (B × A)
commIso = record { to   = λ { (a , b) → b , a }
                 ; from = λ { (b , a) → a , b }
                 ; to-from-inverse = frefl
                 ; from-to-inverse = frefl }

fstIso : {A B : Set} (i : Iso A B) → {C : A → Set} → Iso (Σ A C) (Σ B (C ∘ Iso.from i))
fstIso i {C} =
  record { to   = λ {(a , c) → to i a , subst C (sym (from-to-inverse i _)) c}
         ; from = λ {(b , c) → from i b , c}
         ; to-from-inverse = λ { (b , c) → cong₂-pair (to-from-inverse i _)
                                                      (elim-≡ (λ eq → subst C eq c ≅ c) hrefl (sym (from-to-inverse i _))) }
         ; from-to-inverse = λ { (a , c) → cong₂-pair (from-to-inverse i _)
                                                      (elim-≡ (λ eq → subst C eq c ≅ c) hrefl (sym (from-to-inverse i _))) } }
  where open Iso
