-- An extensional equivalence relation on ornaments, which extends to extensional equivalence on ornamental forgetful maps.

module Ornament.Equivalence where

open import Prelude.Equality
open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Description.HorizontalEquivalence
open import Ornament

open import Function using (id; const; _∘_; type-signature)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_) renaming (map to _**_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl; cong to hcong)


ROrnEq : ∀ {I J} {e e' : J → I} {D E} → ROrn e D E → ∀ {D' E'} → ROrn e' D' E' → Set₁
ROrnEq {I} {J} {e} {e'} {D} {E} O {D'} {E'} O' =
  (X : I → Set) (xs : ⟦ E ⟧ (X ∘ e)) (xs' : ⟦ E' ⟧ (X ∘ e')) → HoriEq E xs E' xs' → HoriEq D (erase O {X} xs) D' (erase O' {X} xs')

ROrnEq-refl : ∀ {I J} {e : J → I} {D E} (O : ROrn e D E) → ROrnEq O O
ROrnEq-refl {E = E} O X xs xs' heq with HoriEq-to-≡ E xs xs' heq
ROrnEq-refl {E = E} O X xs .xs heq | refl = HoriEq-refl

ROrnEq-sym : ∀ {I J} {e e' : J → I} {D E} (O : ROrn e D E) {D' E'} (P : ROrn e' D' E') → ROrnEq O P → ROrnEq P O
ROrnEq-sym O P oeq X xs xs' heq = HoriEq-sym (oeq X xs' xs (HoriEq-sym heq))

ROrnEq-trans-aux :
  {J : Set} (X Y Z : J → Set) → X ≐ Y →
  ∀ {E} (xs : ⟦ E ⟧ X) (zs : ⟦ E ⟧ Z) → HoriEq E xs E zs → Σ[ ys ∶ ⟦ E ⟧ Y ] HoriEq E xs E ys × HoriEq E ys E zs
ROrnEq-trans-aux X Y Z XYeq .tt       .tt         ∎                      = tt , ∎ , ∎
ROrnEq-trans-aux X Y Z XYeq x         z           (ṿ {j} heq)            =
  subst id (XYeq j) x , ṿ (elim-≡ (λ eq → x ≅ subst id eq x) hrefl (XYeq j)) , ṿ (elim-≡ (λ eq → subst id eq x ≅ z) heq (XYeq j))
ROrnEq-trans-aux X Y Z XYeq .(s , xs) .(s , zs) (σ s {xs = xs} {zs} heq) =
  let (ys , xsheq , zsheq) = ROrnEq-trans-aux X Y Z XYeq xs zs heq in (s , ys) , σ s xsheq , σ s zsheq
ROrnEq-trans-aux X Y Z XYeq (xs , xs') (zs , zs') (heq * heq')           =
  let (ys  , xsheq  , zsheq ) = ROrnEq-trans-aux X Y Z XYeq xs  zs  heq
      (ys' , xsheq' , zsheq') = ROrnEq-trans-aux X Y Z XYeq xs' zs' heq'
  in  (ys , ys') , xsheq * xsheq' , zsheq * zsheq'

ROrnEq-trans :
  ∀ {I J} {e e' e'' : J → I} → e ≐ e' →
  ∀ {D E} (O : ROrn e D E) {D'} (P : ROrn e' D' E) {D''} (Q : ROrn e'' D'' E) → ROrnEq O P → ROrnEq P Q → ROrnEq O Q
ROrnEq-trans {e = e} {e'} {e''} eeq O P Q oeq oeq' X xs xs'' heq =
  let (xs' , xsheq , xsheq'') = ROrnEq-trans-aux (X ∘ e) (X ∘ e') (X ∘ e'') (cong X ∘ eeq) xs xs'' heq
  in  HoriEq-trans (oeq X xs xs' xsheq) (oeq' X xs' xs'' xsheq'')

OrnEq : ∀ {I J} {e e' : J → I} {D E} → Orn e D E → Orn e' D E → Set₁
OrnEq {I} {J} {e} {e'} (wrap O) (wrap O') = (e ≐ e') × (∀ j → ROrnEq (O (ok j)) (O' (ok j)))

OrnEq-refl : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → OrnEq O O
OrnEq-refl (wrap O) = frefl , λ j → ROrnEq-refl (O (ok j))

OrnEq-sym : ∀ {I J} {e f : J → I} {D E} (O : Orn e D E) (P : Orn f D E) → OrnEq O P → OrnEq P O
OrnEq-sym (wrap O) (wrap P) (eeq , oeq) = fsym eeq , λ j → ROrnEq-sym (O (ok j)) (P (ok j)) (oeq j)

OrnEq-trans : ∀ {I J} {e f g : J → I} {D E} (O : Orn e D E) (P : Orn f D E) (Q : Orn g D E) → OrnEq O P → OrnEq P Q → OrnEq O Q
OrnEq-trans (wrap O) (wrap P) (wrap Q) (eeq , oeq) (eeq' , oeq') =
  ftrans eeq eeq' , λ j → ROrnEq-trans eeq (O (ok j)) (P (ok j)) (Q (ok j)) (oeq j) (oeq' j)

OrnEq-forget : ∀ {I J} {e e' : J → I} {D E} (O : Orn e D E) (O' : Orn e' D E) → OrnEq O O' → ∀ {j} (x : μ E j) → forget O x ≅ forget O' x
OrnEq-forget {I} {J} {e} {e'} {D} {E} O O' (eeq , eraseeq) =
  induction E (λ x → forget O x ≅ forget O' x) (λ {j} es all → aux j es all refl refl)
  where aux'' : (E' : RDesc J) (es : ⟦ E' ⟧ (μ E)) (all : All E' (λ x → forget O x ≅ forget O' x) es) →
                HoriEq E' (mapFold E E' (ornAlg O) es) E' (mapFold E E' (ornAlg O') es)
        aux'' ∎          es         all          = ∎
        aux'' (ṿ i)      es         all          = ṿ all
        aux'' (σ S E')   (s , es)   all          = σ s (aux'' (E' s) es all)
        aux'' (E' * E'') (es , es') (all , all') = aux'' E' es all * aux'' E'' es' all'
        aux' : ∀ {i'} j → (es : ⟦ E at j ⟧ (μ E)) (all : All (E at j) (λ x → forget O x ≅ forget O' x) es) →
               (eq' : e' j ≡ i') →
               erase (Orn.comp O (ok j)) {μ D} (mapFold E (E at j) (ornAlg O) es)
                 ≅ subst (Ḟ D (μ D)) eq' (erase (Orn.comp O' (ok j)) (mapFold E (E at j) (ornAlg O') es))
        aux' j es all refl = HoriEq-to-≅ (D at e j) (D at e' j) (cong (Desc.comp D) (eeq j))
                                         (erase (Orn.comp O (ok j)) {μ D} (mapFold E (E at j) (ornAlg O) es))
                                         (erase (Orn.comp O' (ok j)) (mapFold E (E at j) (ornAlg O') es))
                                         (eraseeq j (μ D) (mapFold E (E at j) (ornAlg O) es)
                                                          (mapFold E (E at j) (ornAlg O') es)
                                                          (aux'' (E at j) es all))
        aux : (j : J) (es : ⟦ E at j ⟧ (μ E)) (all : All (E at j) (λ x → forget O x ≅ forget O' x) es) →
              ∀ {i} (eq : e j ≡ i) → ∀ {i'} (eq' : e' j ≡ i') →
              con {D = D} (subst (Ḟ D (μ D)) eq (erase (Orn.comp O (ok j)) (mapFold E (E at j) (ornAlg O) es)))
                ≅ con {D = D} (subst (Ḟ D (μ D)) eq' (erase (Orn.comp O' (ok j)) (mapFold E (E at j) (ornAlg O') es)))
        aux j es all eq eq' with trans (trans (sym eq) (eeq j)) eq'
        aux j es all refl eq' | refl = hcong con (aux' j es all eq')
