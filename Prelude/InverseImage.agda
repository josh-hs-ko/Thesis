-- Definition of inverse images of a function, and definitions of set-theoretic pullbacks in terms of inverse images and quotients.

module Prelude.InverseImage where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Function
open import Prelude.Product

open import Function using (_∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡) renaming (refl to hrefl)


--------
-- inverse images

data _⁻¹_ {A B : Set} (f : A → B) : B → Set where
  ok : (x : A) → f ⁻¹ (f x)

InvImage : {A B : Set} → (A → B) → B → Set
InvImage = _⁻¹_

und : ∀ {A B} {f : A → B} {y} → f ⁻¹ y → A
und (ok x) = x

und-proj₁ : {A : Set} {B : A → Set} {x : A} → proj₁ {A = A} {B} ⁻¹ x → B x
und-proj₁ (ok (x , y)) = y

from≡ : ∀ {A B} (f : A → B) {x y} → f x ≡ y → f ⁻¹ y
from≡ f {x} refl = ok x

to≡ : ∀ {A B} {f : A → B} {y} → (x : f ⁻¹ y) → f (und x) ≡ y
to≡ (ok x) = refl

und-from≡ : ∀ {A B} (f : A → B) {x y} → (eq : f x ≡ y) → und (from≡ f eq) ≡ x
und-from≡ f refl = refl

und≡' : {A B : Set} {f : A → B} {x : A} {y : B} (x' : f ⁻¹ y) → x ≡ und x' → ok {f = f} x ≅ x'
und≡' (ok x') refl = hrefl

und≡ : {A B : Set} {f : A → B} {y : B} {x x' : f ⁻¹ y} → und x ≡ und x' → x ≡ x'
und≡ {f = f} {x = ok x} {x'} eq = ≅-to-≡ (und≡' x' eq)

elim-⁻¹ : {A B : Set} {f : A → B} (P : ∀ {b} → f ⁻¹ b → Set) → (∀ a → P (ok a)) → ∀ {b} (a : f ⁻¹ b) → P a
elim-⁻¹ P p (ok a) = p a

ok-und : {A B : Set} {f : A → B} {y : B} (x : f ⁻¹ y) → ok {f = f} (und x) ≅ x
ok-und (ok x) = hrefl


--------
-- set-theoretic pullbacks

record _⋈_ {A B C : Set} (f : A → C) (g : B → C) : Set where
  constructor _,_
  field
    {c} : C
    a   : f ⁻¹ c
    b   : g ⁻¹ c

infixr 4 _,_

pull : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → C
pull = _⋈_.c

pproj₁ : {A B C : Set} {f : A → C} {g : B → C} → (p : f ⋈ g) → f ⁻¹ (pull p)
pproj₁ = _⋈_.a

pproj₂ : {A B C : Set} {f : A → C} {g : B → C} → (p : f ⋈ g) → g ⁻¹ (pull p)
pproj₂ = _⋈_.b

π₁ : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → A
π₁ = und ∘ pproj₁

π₂ : {A B C : Set} {f : A → C} {g : B → C} → f ⋈ g → B
π₂ = und ∘ pproj₂

decouple : {A B C : Set} {f : A → C} {g : B → C} {p q : f ⋈ g} → π₁ p ≡ π₁ q → π₂ p ≡ π₂ q → p ≡ q
decouple {f = f} {g} {ok a , b} {ok .a , b'} refl eq = cong (_,_ {c = f a} (ok a)) (≅-to-≡ (aux b b' eq))
  where aux : ∀ {c c'} (b : g ⁻¹ c) (b' : g ⁻¹ c') → und b ≡ und b' → b ≅ b'
        aux (ok b) (ok .b) refl = hrefl

⋈-square : {A B C : Set} (f : A → C) (g : B → C) → Square Fun (slice A f) (slice B g)
⋈-square f g = span (slice (f ⋈ g) pull) (sliceMorphism π₁ (λ { (ok a , b) → refl })) (sliceMorphism π₂ (λ { (a , ok b) → refl }))

⋈-is-pullback : {A B C : Set} (f : A → C) (g : B → C) → Pullback Fun (slice A f) (slice B g) (⋈-square f g)
⋈-is-pullback {A} {B} {C} f g s =
  spanMorphism (sliceMorphism (λ t → from≡ f (SliceMorphism.triangle (Span.l s) t) , from≡ g (SliceMorphism.triangle (Span.r s) t)) frefl)
               (λ t → und-from≡ f (SliceMorphism.triangle (Span.l s) t))
               (λ t → und-from≡ g (SliceMorphism.triangle (Span.r s) t)) ,
  (λ m t → decouple (trans (und-from≡ f (SliceMorphism.triangle (Span.l s) t)) (sym (SpanMorphism.triangle-l m t)))
                    (trans (und-from≡ g (SliceMorphism.triangle (Span.r s) t)) (sym (SpanMorphism.triangle-r m t))))


--------
-- canonical set-theoretic pullback

STP-square : {A B C : Set} (f : A → C) (g : B → C) → Square Fun (slice A f) (slice B g)
STP-square {A} {B} {C} f g = span (slice (Σ[ p ∈ A × B ] f (proj₁ p) ≡ g (proj₂ p)) (g ∘ proj₂ ∘ proj₁))
                                  (sliceMorphism (proj₁ ∘ proj₁) proj₂)
                                  (sliceMorphism (proj₂ ∘ proj₁) frefl)

STP-decouple : {A B C : Set} (f : A → C) (g : B → C) → let s = STP-square f g in {p q : Square-T s} →
               SliceMorphism.m (Span.l s) p ≡ SliceMorphism.m (Span.l s) q → SliceMorphism.m (Span.r s) p ≡ SliceMorphism.m (Span.r s) q → p ≡ q
STP-decouple f g leq req = cong₂-pair (cong₂ _,_ leq req) (proof-irrelevance' (cong f leq) (cong g req))

STP-is-pullback : {A B C : Set} (f : A → C) (g : B → C) → Pullback Fun (slice A f) (slice B g) (STP-square f g)
STP-is-pullback f g s = spanMorphism (sliceMorphism (λ p → (SliceMorphism.m (Span.l s) p , SliceMorphism.m (Span.r s) p) ,
                                                           trans (SliceMorphism.triangle (Span.l s) p) (sym (SliceMorphism.triangle (Span.r s) p)))
                                                    (SliceMorphism.triangle (Span.r s))) frefl frefl ,
                        λ m p → STP-decouple f g (sym (SpanMorphism.triangle-l m p)) (sym (SpanMorphism.triangle-r m p))

decouple' : {A B C : Set} (f : A → C) (g : B → C) (s : Square Fun (slice A f) (slice B g)) → Pullback Fun (slice A f) (slice B g) s →
            {p q : Square-T s} → SliceMorphism.m (Span.l s) p ≡ SliceMorphism.m (Span.l s) q → SliceMorphism.m (Span.r s) p ≡ SliceMorphism.m (Span.r s) q → p ≡ q
decouple' f g s ps {p} {q} leq req =
  let iso = pullback-iso Fun (slice _ f) (slice _ g) s (STP-square f g) ps (STP-is-pullback f g)
  in  trans (sym (Iso.from-to-inverse iso p)) (trans (cong (Iso.from iso) (STP-decouple f g leq req)) (Iso.from-to-inverse iso q))
