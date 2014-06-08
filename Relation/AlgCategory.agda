-- Let `D : Desc I` be a description.
-- The category `RAlg D` is the wide subcategory of the category of relational `D`-algebras where the morphisms are restricted to be functions and are proof-relevant.
-- This module also defines the banana-split algebras and proves that they are products in `RAlg D`.

open import Description

module Relation.AlgCategory {I : Set} (D : Desc I) where

open import Prelude.Equality
open import Prelude.Product
open import Prelude.Category
open import Prelude.Category.Span
open import Prelude.Function
open import Prelude.Function.Fam
open import Relation
open import Relation.CompChain

open import Function using (id; _∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; <_,_>)
open import Relation.Binary using (Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-subst-removable; module ≅-Reasoning)
                                                  renaming (refl to hrefl; trans to htrans; sym to hsym)

record RAlgebra : Set₁ where
  constructor _,_
  field
    Carrier : I → Set
    R       : Ḟ D Carrier ↝ Carrier

Hom : RAlgebra → RAlgebra → Set
Hom R S = RAlgebra.Carrier R ⇉ RAlgebra.Carrier S

HomComm : (R S : RAlgebra) → Hom R S → Set
HomComm R S h = (i : I) (xs : Ḟ D (RAlgebra.Carrier R) i) (x : RAlgebra.Carrier R i) →
                (RAlgebra.R R !!) i xs x → (RAlgebra.R S !!) i (Ḟ-map D h xs) (h x)

record RAlgMorphism (R S : RAlgebra) : Set₁ where
  constructor _,_
  field
    h : Hom R S
    c : HomComm R S h

RAlgMorphism-id-comm : {R : RAlgebra} → HomComm R R id
RAlgMorphism-id-comm {X , R} i xs x r = subst (λ xs' → (R !!) i xs' x) (sym (Ḟ-map-preserves-id D i xs)) r

RAlgMorphism-id : {R : RAlgebra} → RAlgMorphism R R
RAlgMorphism-id {X , R} = id , RAlgMorphism-id-comm

RAlgMorphism-comp-comm : {R S T : RAlgebra} (m : RAlgMorphism S T) (n : RAlgMorphism R S) → HomComm R T (RAlgMorphism.h m ∘ RAlgMorphism.h n)
RAlgMorphism-comp-comm {X , R} {Y , S} {Z , T} (g , cg) (h , ch) i xs x r =
  subst (λ zs → (T !!) i zs (g (h x))) (sym (Ḟ-map-preserves-comp D g h i xs)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))

RAlgMorphism-comp : {R S T : RAlgebra} → RAlgMorphism S T → RAlgMorphism R S → RAlgMorphism R T
RAlgMorphism-comp {R} {S} {T} m n = RAlgMorphism.h m ∘ RAlgMorphism.h n , RAlgMorphism-comp-comm m n

HomCommEq : {R S : RAlgebra} → RAlgMorphism R S → RAlgMorphism R S → Set
HomCommEq {X , R} {Y , S} (g , cg) (h , ch) = (i : I) (xs : Ḟ D X i) (x : X i) (r : (R !!) i xs x) → cg i xs x r ≅ ch i xs x r

RAlgMorphismEq : {R S : RAlgebra} → RAlgMorphism R S → RAlgMorphism R S → Set
RAlgMorphismEq m n = ({i : I} → RAlgMorphism.h m {i} ≐ RAlgMorphism.h n {i}) × HomCommEq m n

RAlgMorphismSetoid : RAlgebra → RAlgebra → Setoid _ _
RAlgMorphismSetoid R S = record
  { Carrier = RAlgMorphism R S
  ; _≈_ = RAlgMorphismEq
  ; isEquivalence = record
      { refl  = λ {m} → frefl , λ i xs x r → hrefl
      ; sym   = λ { (heq , ceq) → fsym heq , λ i xs x r → hsym (ceq i xs x r) }
      ; trans = λ { {m} {n} {l} (heq , ceq) (heq' , ceq') → ftrans heq heq' , λ i xs x r → htrans (ceq i xs x r) (ceq' i xs x r) } } }

id-l-comm : {R S : RAlgebra} (m : RAlgMorphism R S) → HomCommEq (RAlgMorphism-comp RAlgMorphism-id m) m
id-l-comm {X , R} {Y , S} (h , c) i xs x r =
  htrans (≡-subst-removable (λ zs → (S !!) i zs (h x)) (sym (Ḟ-map-preserves-comp D id h i xs))
            (subst (λ xs' → (S !!) i xs' (h x)) (sym (Ḟ-map-preserves-id D i (Ḟ-map D h xs))) (c i xs x r)))
         (≡-subst-removable (λ xs' → (S !!) i xs' (h x)) (sym (Ḟ-map-preserves-id D i (Ḟ-map D h xs))) (c i xs x r))

id-r-comm : {R S : RAlgebra} (m : RAlgMorphism R S) → HomCommEq (RAlgMorphism-comp m RAlgMorphism-id) m
id-r-comm {X , R} {Y , S} (h , c) i xs x r =
  htrans (≡-subst-removable (λ zs → (S !!) i zs (h x)) (sym (Ḟ-map-preserves-comp D h id i xs))
            (c i (Ḟ-map D id xs) x (subst (λ xs' → (R !!) i xs' x) (sym (Ḟ-map-preserves-id D i xs)) r)))
         (elim-≡ (λ {xs'} eq → c i xs' x (subst (λ xs'' → (R !!) i xs'' x) eq r) ≅ c i xs x r) hrefl (sym (Ḟ-map-preserves-id D i xs)))

assoc-comm : {R S T U : RAlgebra} (m : RAlgMorphism T U) (n : RAlgMorphism S T) (l : RAlgMorphism R S) →
             HomCommEq (RAlgMorphism-comp (RAlgMorphism-comp m n) l) (RAlgMorphism-comp m (RAlgMorphism-comp n l))
assoc-comm {X , R} {Y , S} {Z , T} {W , U} (f , cf) (g , cg) (h , ch) i xs x r =
  begin
      subst (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D (f ∘ g) h i xs))
        (subst (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f g i (Ḟ-map D h xs)))
           (cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))))
    ≅⟨ ≡-subst-removable (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D (f ∘ g) h i xs))
                         (subst (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f g i (Ḟ-map D h xs)))
                            (cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r)))) ⟩
      subst (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f g i (Ḟ-map D h xs)))
        (cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r)))
    ≅⟨ ≡-subst-removable (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f g i (Ḟ-map D h xs)))
                         (cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))) ⟩
      cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))
    ≅⟨ elim-≡ (λ {zs'} eq → cf i (Ḟ-map D g (Ḟ-map D h xs)) (g (h x)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))
                          ≅ cf i zs' (g (h x)) (subst (λ zs → (T !!) i zs (g (h x))) eq (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))))
              hrefl (sym (Ḟ-map-preserves-comp D g h i xs)) ⟩
      cf i (Ḟ-map D (g ∘ h) xs) (g (h x))
         (subst (λ zs → (T !!) i zs (g (h x))) (sym (Ḟ-map-preserves-comp D g h i xs)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r)))
    ≅⟨ hsym (≡-subst-removable (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f (g ∘ h) i xs))
                               (cf i (Ḟ-map D (g ∘ h) xs) (g (h x))
                                   (subst (λ zs → (T !!) i zs (g (h x))) (sym (Ḟ-map-preserves-comp D g h i xs))
                                      (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))))) ⟩
      subst (λ zs → (U !!) i zs (f (g (h x)))) (sym (Ḟ-map-preserves-comp D f (g ∘ h) i xs))
        (cf i (Ḟ-map D (g ∘ h) xs) (g (h x))
            (subst (λ zs → (T !!) i zs (g (h x))) (sym (Ḟ-map-preserves-comp D g h i xs)) (cg i (Ḟ-map D h xs) (h x) (ch i xs x r))))
  ∎
  where open ≅-Reasoning

cong-l-comm : {R S T : RAlgebra} (m : RAlgMorphism S T) (n l : RAlgMorphism R S) →
              RAlgMorphismEq n l → HomCommEq (RAlgMorphism-comp m n) (RAlgMorphism-comp m l)
cong-l-comm {X , R} {Y , S} {Z , T} (f , cf) (g , cg) (h , ch) (gheq , cgheq) i xs x r =
  htrans (≡-subst-removable (λ zs → (T !!) i zs (f (g x))) (sym (Ḟ-map-preserves-comp D f g i xs)) (cf i (Ḟ-map D g xs) (g x) (cg i xs x r)))
         (htrans (aux (Ḟ-map-preserves-eq D g h gheq i xs) (gheq x) (cgheq i xs x r))
                 (hsym (≡-subst-removable (λ zs → (T !!) i zs (f (h x))) (sym (Ḟ-map-preserves-comp D f h i xs))
                                          (cf i (Ḟ-map D h xs) (h x) (ch i xs x r)))))
  where
    aux : {ys : Ḟ D Y i} (yseq : ys ≡ Ḟ-map D h xs) {y : Y i} (yeq : y ≡ h x) {s : (S !!) i ys y} (seq : s ≅ ch i xs x r) →
          cf i ys y s ≅ cf i (Ḟ-map D h xs) (h x) (ch i xs x r)
    aux refl refl hrefl = hrefl

cong-r-comm : {R S T : RAlgebra} (m n : RAlgMorphism S T) (l : RAlgMorphism R S) →
              RAlgMorphismEq m n → HomCommEq (RAlgMorphism-comp m l) (RAlgMorphism-comp n l)
cong-r-comm {X , R} {Y , S} {Z , T} (f , cf) (g , cg) (h , ch) (fgeq , cfgeq) i xs x r =
  htrans (≡-subst-removable (λ zs → (T !!) i zs (f (h x))) (sym (Ḟ-map-preserves-comp D f h i xs)) (cf i (Ḟ-map D h xs) (h x) (ch i xs x r)))
         (htrans (cfgeq i (Ḟ-map D h xs) (h x) (ch i xs x r))
                 (hsym (≡-subst-removable (λ zs → (T !!) i zs (g (h x))) (sym (Ḟ-map-preserves-comp D g h i xs))
                                          (cg i (Ḟ-map D h xs) (h x) (ch i xs x r)))))

RAlg : Category
RAlg = record
  { Object   = RAlgebra
  ; Morphism = RAlgMorphismSetoid
  ; _·_ = RAlgMorphism-comp
  ; id  = RAlgMorphism-id
  ; id-l   = λ { m → frefl , id-l-comm m }
  ; id-r   = λ { m → frefl , id-r-comm m }
  ; assoc  = λ { m n l → frefl , assoc-comm m n l }
  ; cong-l = λ { {R} {S} {T} {n} {l} m nleq → fcong-l (RAlgMorphism.h m) (proj₁ nleq) , cong-l-comm m n l nleq }
  ; cong-r = λ { {R} {S} {T} {m} {n} l mneq → fcong-r (RAlgMorphism.h l) (proj₁ mneq) , cong-r-comm m n l mneq } }


--------
-- banana-split algebras

bs-alg : RAlgebra → RAlgebra → RAlgebra
bs-alg (X , R) (Y , S) = X ×' Y , wrap λ { i xys (x , y) → (R !!) i (Ḟ-map D proj₁ xys) x × (S !!) i (Ḟ-map D proj₂ xys) y }

bs-alg-proj-l : (R S : RAlgebra) → RAlgMorphism (bs-alg R S) R
bs-alg-proj-l (X , R) (Y , S) = proj₁ , λ i xys xy → proj₁

bs-alg-proj-r : (R S : RAlgebra) → RAlgMorphism (bs-alg R S) S
bs-alg-proj-r (X , R) (Y , S) = proj₂ , λ i xys xy → proj₂

bs-alg-span : (R S : RAlgebra) → Span RAlg R S
bs-alg-span R S = span (bs-alg R S) (bs-alg-proj-l R S) (bs-alg-proj-r R S)

bs-alg-product : (R S : RAlgebra) → Product RAlg R S (bs-alg-span R S)
bs-alg-product (X , R) (Y , S) (span (Z , T) (l , cl) (r , cr)) =
  spanMorphism (< l , r > , λ i zs z t → subst (λ xs → (R !!) i xs (l z)) (Ḟ-map-preserves-comp D proj₁ < l , r > i zs) (cl i zs z t) ,
                                         subst (λ ys → (S !!) i ys (r z)) (Ḟ-map-preserves-comp D proj₂ < l , r > i zs) (cr i zs z t))
               (frefl , λ i zs z t → htrans (≡-subst-removable (λ xs → (R !!) i xs (l z)) (sym (Ḟ-map-preserves-comp D proj₁ < l , r > i zs))
                                               (subst (λ xs → (R !!) i xs (l z)) (Ḟ-map-preserves-comp D proj₁ < l , r > i zs) (cl i zs z t)))
                                            (≡-subst-removable (λ xs → (R !!) i xs (l z)) (Ḟ-map-preserves-comp D proj₁ < l , r > i zs) (cl i zs z t)))
               (frefl , λ i zs z t → htrans (≡-subst-removable (λ ys → (S !!) i ys (r z)) (sym (Ḟ-map-preserves-comp D proj₂ < l , r > i zs))
                                               (subst (λ ys → (S !!) i ys (r z)) (Ḟ-map-preserves-comp D proj₂ < l , r > i zs) (cr i zs z t)))
                                            (≡-subst-removable (λ ys → (S !!) i ys (r z)) (Ḟ-map-preserves-comp D proj₂ < l , r > i zs) (cr i zs z t))) ,
  λ { (spanMorphism (h , c) (hleq , cleq) (hreq , creq)) →
      (λ z → cong₂ _,_ (sym (hleq z)) (sym (hreq z))) ,
      (λ i zs z t → hcong₂-pair
                      (htrans (htrans (≡-subst-removable (λ xs → (R !!) i xs (l z)) (Ḟ-map-preserves-comp D proj₁ < l , r > i zs) (cl i zs z t))
                                      (hsym (cleq i zs z t)))
                              (≡-subst-removable (λ xs → (R !!) i xs (proj₁ (h z))) (sym (Ḟ-map-preserves-comp D proj₁ h i zs)) (proj₁ (c i zs z t))))
                      (htrans (htrans (≡-subst-removable (λ ys → (S !!) i ys (r z)) (Ḟ-map-preserves-comp D proj₂ < l , r > i zs) (cr i zs z t))
                                      (hsym (creq i zs z t)))
                              (≡-subst-removable (λ ys → (S !!) i ys (proj₂ (h z))) (sym (Ḟ-map-preserves-comp D proj₂ h i zs)) (proj₂ (c i zs z t))))) }
