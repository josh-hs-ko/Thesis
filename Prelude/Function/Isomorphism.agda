-- Various ways to construct isomorphisms in `Fun`.

module Prelude.Function.Isomorphism where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Function
open import Prelude.Product
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.InverseImage

open import Level
open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂) renaming (map to _**_)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡; ≡-to-≅; ≡-subst-removable)
                                                  renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans)


--------
-- isomorphisms in Fun

mkIso : ∀ {A B} → (f : A → B) → (∀ x x' → f x ≡ f x' → x ≡ x') → (g : (y : B) → Σ[ x ∈ A ] f x ≡ y) → Iso A B
mkIso f f-inj g =
  record { to   = f
         ; from = proj₁ ∘ g
         ; to-from-inverse = λ y → proj₂ (g y)
         ; from-to-inverse = λ x → f-inj (proj₁ (g (f x))) x (proj₂ (g (f x))) }

mkIso' : ∀ {A B} → (f : A → B) (g : (b : B) → f ⁻¹ b) → (∀ {b} (a : f ⁻¹ b) → g b ≡ a) → Iso A B
mkIso' f g un =
  record { to   = f
         ; from = und ∘ g
         ; to-from-inverse = see-below
         ; from-to-inverse = λ j → cong und (un (ok j)) }
  where see-below : ∀ b → f (und (g b)) ≡ b
        see-below b with g b
        see-below ._ | ok a = refl

compIso : {I J : Set} {X : I → Set} {Y : J → Set} (iso : Iso (Σ I X) (Σ J Y)) →
          (e : I → J) (u : ∀ {i} → X i → Y (e i)) → Iso.to iso ≐ (e ** u) →
          (Z : J → Set) (ziso : ∀ {j} → Iso (Z j) (Σ[ i ∈ I ] e i ≡ j)) →
          (g : ∀ {j} → (y : Y j) → Z j) (fgeq : ∀ {j} (y : Y j) → proj₁ (Iso.from iso (j , y)) ≡ proj₁ (Iso.to ziso (g y))) →
          ∀ j → Iso (Σ (Z j) (X ∘ proj₁ ∘ Iso.to ziso)) (Y j)
compIso {I} {J} {X} {Y} iso e u toeq Z ziso g fgeq j =
  record { to   = λ {(z , x) → subst Y (proj₂ (Iso.to ziso z)) (u x)}
         ; from = λ y → g y , subst X (fgeq y) (proj₂ (Iso.from iso (j , y)))
         ; to-from-inverse =
             λ y → ≅-to-≡ (htrans (≡-subst-removable Y (proj₂ (Iso.to ziso (g y))) _)
                                  (elim-≡ (λ eq → u (subst X eq (proj₂ (Iso.from iso (j , y)))) ≅ y)
                                          (hcong proj₂ (≡-to-≅ (inv (j , y)))) (fgeq y)))
         ; from-to-inverse =
             λ { (z , x) →
                 cong₂-pair
                   (begin
                      g (subst Y (proj₂ (Iso.to ziso z)) (u x))
                        ≡⟨ sym (Iso.from-to-inverse ziso _) ⟩
                      Iso.from ziso (Iso.to ziso (g (subst Y (proj₂ (Iso.to ziso z)) (u x))))
                        ≡⟨ refl ⟩
                      Iso.from ziso (proj₁ (Iso.to ziso (g (subst Y (proj₂ (Iso.to ziso z)) (u x)))) ,
                                     proj₂ (Iso.to ziso (g (subst Y (proj₂ (Iso.to ziso z)) (u x)))))
                        ≡⟨ (let eq = sym (fgeq (subst Y (proj₂ (Iso.to ziso z)) (u x)))
                            in  cong (Iso.from ziso) (cong₂-pair eq (proof-irrelevance' (cong e eq) refl))) ⟩
                      Iso.from ziso (proj₁ (Iso.from iso (_ , subst Y (proj₂ (Iso.to ziso z)) (u x))) ,
                                     cong proj₁ (inv (j , subst Y (proj₂ (Iso.to ziso z)) (u x))))
                        ≡⟨ (let eq = cong (proj₁ ∘ Iso.from iso)
                                       (cong₂-pair (sym (proj₂ (Iso.to ziso z))) (≡-subst-removable Y (proj₂ (Iso.to ziso z)) (u x)))
                            in cong (Iso.from ziso) (cong₂-pair eq (proof-irrelevance' (cong e eq) refl))) ⟩
                      Iso.from ziso (proj₁ (Iso.from iso (e (proj₁ (Iso.to ziso z)) , u x)) ,
                                     trans (cong proj₁ (inv (e (proj₁ (Iso.to ziso z)) , u x))) (proj₂ (Iso.to ziso z)))
                        ≡⟨ (let eq = cong (proj₁ ∘ Iso.from iso) (sym (toeq (proj₁ (Iso.to ziso z) , x)))
                            in  cong (Iso.from ziso) (cong₂-pair eq (proof-irrelevance' (cong e eq) refl))) ⟩
                      Iso.from ziso (proj₁ (Iso.from iso (Iso.to iso (proj₁ (Iso.to ziso z) , x))) ,
                                     trans (cong (e ∘ proj₁) (Iso.from-to-inverse iso (proj₁ (Iso.to ziso z) , x))) (proj₂ (Iso.to ziso z)))
                        ≡⟨ (let eq = cong proj₁ (Iso.from-to-inverse iso (proj₁ (Iso.to ziso z) , x))
                            in  cong (Iso.from ziso) (cong₂-pair eq (proof-irrelevance' (cong e eq) refl))) ⟩
                      Iso.from ziso (proj₁ (Iso.to ziso z) , proj₂ (Iso.to ziso z))
                        ≡⟨ refl ⟩
                      Iso.from ziso (Iso.to ziso z)
                        ≡⟨ Iso.from-to-inverse ziso z ⟩
                      z
                    ∎)
                   (htrans
                      (≡-subst-removable X (fgeq (subst Y (proj₂ (Iso.to ziso z)) (u x)))
                                           (proj₂ (Iso.from iso (j , subst Y (proj₂ (Iso.to ziso z)) (u x)))))
                      (elim-≡ (λ {j'} eq → proj₂ (Iso.from iso (j' , subst Y eq (u x))) ≅ x)
                              (hcong proj₂ (≡-to-≅ (trans (sym (cong (Iso.from iso) (toeq (proj₁ (Iso.to ziso z) , x))))
                                                          (Iso.from-to-inverse iso (proj₁ (Iso.to ziso z) , x)))))
                              (proj₂ (Iso.to ziso z))))} }
  where open ≡-Reasoning
        inv : (e ** u) ∘ Iso.from iso ≐ id
        inv = ftrans (fcong-r (Iso.from iso) (fsym toeq)) (Iso.to-from-inverse iso)

{-

compIso : {I J : Set} {X : I → Set} {Y : J → Set} (iso : Iso (Σ I X) (Σ J Y)) →
          (e : I → J) (u : ∀ {i} → X i → Y (e i)) → Iso.to iso ≐ (e ** u) →
          ∀ j → Iso (Σ (e ⁻¹ j) (X ∘ und)) (Y j)
compIso {I} {J} {X} {Y} iso e u eq j =
  record { to = to; from = from; to-from-inverse = to-from-inverse; from-to-inverse = from-to-inverse }
  where
    to : ∀ {j} → Σ (e ⁻¹ j) (X ∘ und) → Y j
    to (ok i , x) = u x
    from : ∀ {j} → Y j → Σ (e ⁻¹ j) (X ∘ und)
    from {j} y = subst (λ j' → Σ (e ⁻¹ j') (X ∘ und))
                       (cong proj₁ (trans (sym (eq (Iso.from iso (j , y)))) (Iso.to-from-inverse iso (j , y))))
                       (ok _ , proj₂ (Iso.from iso (j , y)))
    to-from-inverse : ∀ {j} → (y : Y j) → to (from y) ≡ y
    to-from-inverse {j} y =
      ≅-to-≡
        (elim-≡ (λ eq' → to (subst (λ j' → Σ (e ⁻¹ j') (X ∘ und)) eq' (ok (proj₁ (Iso.from iso (j , y))) , proj₂ (Iso.from iso (j , y)))) ≅ y)
                (hcong proj₂ (≡-to-≅ (trans (sym (eq (Iso.from iso (j , y)))) (Iso.to-from-inverse iso (j , y)))))
                (cong proj₁ (trans (sym (eq (Iso.from iso (j , y)))) (Iso.to-from-inverse iso (j , y)))))
    from-to-inverse : ∀ {j} → (x : Σ (e ⁻¹ j) (X ∘ und)) → from (to x) ≡ x
    from-to-inverse (ok i , x) =
      ≅-to-≡
        (elim-≡ (λ eq' → subst (λ j' → Σ (e ⁻¹ j') (X ∘ und)) eq' (ok (proj₁ (Iso.from iso (e i , u x))) , proj₂ (Iso.from iso (e i , u x)))
                           ≅ (ok i , x ∈ Σ (e ⁻¹ e i) (X ∘ und)))
                (subst (λ y' → (ok (proj₁ y') , proj₂ y' ∈ Σ (e ⁻¹ e (proj₁ y')) (X ∘ und))
                                 ≅ (ok i , x ∈ Σ (e ⁻¹ e i) (X ∘ und)))
                       (trans (sym (Iso.from-to-inverse iso (i , x))) (cong (Iso.from iso) (eq (i , x))))
                       hrefl)
                (cong proj₁ (trans (sym (eq (Iso.from iso (e i , u x)))) (Iso.to-from-inverse iso (e i , u x)))))

-}
