-- Definition of inverse images of a function, and definition of set-theoretic pullbacks in terms of inverse images.

module Thesis.Prelude.InverseImage where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Category.Span
open import Thesis.Prelude.Category.Pullback
open import Thesis.Prelude.Function

open import Function using (_∘_; type-signature)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡) renaming (refl to hrefl)


--------
-- inverse images

data _⁻¹_ {A B : Set} (f : A → B) : B → Set where
  ok : (x : A) → f ⁻¹ (f x)

und : ∀ {A B} {f : A → B} {y} → f ⁻¹ y → A
und (ok x) = x

from≡ : ∀ {A B} {f : A → B} {x y} → f x ≡ y → f ⁻¹ y
from≡ {x = x} refl = ok x

to≡ : ∀ {A B} {f : A → B} {y} → (x : f ⁻¹ y) → f (und x) ≡ y
to≡ (ok x) = refl

und-from≡ : ∀ {A B} {f : A → B} {x y} → (eq : f x ≡ y) → und (from≡ {f = f} eq) ≡ x
und-from≡ refl = refl

und≡ : ∀ {A B} {f : A → B} {y} {x x' : f ⁻¹ y} → und x ≡ und x' → x ≡ x'
und≡ {f = f} {x = ok x} {x'} eq = ≅-to-≡ (aux x' eq)
  where aux : ∀ {x y} (x' : f ⁻¹ y) → x ≡ und x' → ok {f = f} x ≅ x'
        aux (ok x') refl = hrefl

elim-⁻¹ : {A B : Set} {f : A → B} (P : ∀ {b} → f ⁻¹ b → Set) → (∀ a → P (ok a)) → ∀ {b} (a : f ⁻¹ b) → P a
elim-⁻¹ P p (ok a) = p a


--------
-- set-theoretic pullbacks

data _⋈_ {A B C : Set} (f : A → C) (g : B → C) : Set where
  _,_ : {c : C} → f ⁻¹ c → g ⁻¹ c → f ⋈ g

infixr 4 _,_

pull : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → C
pull (_,_ {c} _ _) = c

π₁ : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → A
π₁ (a , _) = und a

π₂ : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → B
π₂ (_ , b) = und b

decouple : {A B C : Set} {f : A → C} {g : B → C} {p q : f ⋈ g} → π₁ p ≡ π₁ q → π₂ p ≡ π₂ q → p ≡ q
decouple {f = f} {g} {ok a , b} {ok .a , b'} refl eq = cong (_,_ {c = f a} (ok a)) (≅-to-≡ (aux b b' eq))
  where aux : ∀ {c c'} (b : g ⁻¹ c) (b' : g ⁻¹ c') → und b ≡ und b' → b ≅ b'
        aux (ok b) (ok .b) refl = hrefl

⋈-is-Pullback : {A B C : Set} (f : A → C) (g : B → C) → Pullback Fun (slice A f) (slice B g) (f ⋈ g)
⋈-is-Pullback {A} {B} {C} f g =
  (span (slice (f ⋈ g) pull) (sliceMorphism π₁ (λ { (ok a , b) → refl })) (sliceMorphism π₂ (λ { (a , ok b) → refl })) , refl) ,
  (λ s → spanMorphism
           (sliceMorphism (λ t → from≡ (SliceMorphism.triangle (Span.l s) t) , from≡ (SliceMorphism.triangle (Span.r s) t)) frefl)
           (λ t → und-from≡ {f = f} (SliceMorphism.triangle (Span.l s) t)) (λ t → und-from≡ {f = g} (SliceMorphism.triangle (Span.r s) t)) ,
         (λ m t → decouple (trans (und-from≡ {f = f} (SliceMorphism.triangle (Span.l s) t)) (sym (SpanMorphism.triangle-l m t)))
                           (trans (und-from≡ {f = g} (SliceMorphism.triangle (Span.r s) t)) (sym (SpanMorphism.triangle-r m t)))))
