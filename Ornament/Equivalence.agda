-- An extensional equivalence relation on ornaments, which extends to extensional equivalence on ornamental forgetful maps.

module Ornament.Equivalence where

open import Prelude.Equality
open import Prelude.Function
open import Prelude.Product
open import Prelude.InverseImage
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.Horizontal

open import Function using (id; flip; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡; ≡-subst-removable)
                                                  renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans)


ROrnEq : {I J : Set} {e e' : J → I} {D D' : RDesc I} {E : RDesc J} → ROrn e D E → ROrn e' D' E → Set
ROrnEq {E = E} O P = (hs : Ṡ E) → erase-Ṡ O hs ≅ erase-Ṡ P hs

ROrnEq-refl : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ROrnEq O O
ROrnEq-refl O hs = hrefl

ROrnEq-sym : {I J : Set} {e e' : J → I} {D D' : RDesc I} {E : RDesc J} (O : ROrn e D E) (P : ROrn e' D' E) → ROrnEq O P → ROrnEq P O
ROrnEq-sym O P roeq hs = hsym (roeq hs)

ROrnEq-trans : {I J : Set} {e e' e'' : J → I} {D D' D'' : RDesc I} {E : RDesc J}
               (O : ROrn e D E) (P : ROrn e' D' E) (Q : ROrn e'' D'' E) → ROrnEq O P → ROrnEq P Q → ROrnEq O Q
ROrnEq-trans O P Q roeq roeq' hs = htrans (roeq hs) (roeq' hs)

OrnEq : ∀ {I J} {e e' : J → I} {D E} → Orn e D E → Orn e' D E → Set
OrnEq {I} {J} {e} {e'} O P = (e ≐ e') × ((j : J) → ROrnEq (Orn.comp O (ok j)) (Orn.comp P (ok j)))

OrnEq-refl : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → OrnEq O O
OrnEq-refl O = frefl , λ j → ROrnEq-refl (Orn.comp O (ok j))

OrnEq-sym : {I J : Set} {e e' : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq P O
OrnEq-sym {D = D} O P (eeq , oeq) = fsym eeq , λ j → ROrnEq-sym (Orn.comp O (ok j)) (Orn.comp P (ok j)) (oeq j)

OrnEq-trans : {I J : Set} {e e' e'' : J → I} {D : Desc I} {E : Desc J}
              (O : Orn e D E) (P : Orn e' D E) (Q : Orn e'' D E) → OrnEq O P → OrnEq P Q → OrnEq O Q
OrnEq-trans {D = D} O P Q (eeq , OPeq) (eeq' , PQeq) =
  ftrans eeq eeq' , λ j → ROrnEq-trans (Orn.comp O (ok j)) (Orn.comp P (ok j)) (Orn.comp Q (ok j)) (OPeq j) (PQeq j)

OrnEq-forget : ∀ {I J} {e e' : J → I} {D E} (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → ∀ {j} (x : μ E j) → forget O x ≅ forget P x
OrnEq-forget {I} {J} {e} {e'} {D} {E} O P (eeq , oeq) = induction E (λ _ x → forget O x ≅ forget P x) (λ j xs ihs → aux j xs ihs refl refl)
  where
    aux''' : (js : List J) (xs : Ṗ js (μ E)) → All-Ṗ (λ _ x → forget O x ≅ forget P x) js xs →
             ṖHEq js (mapFold-Ṗ E (ornAlg O) js xs) (mapFold-Ṗ E (ornAlg P) js xs)
    aux''' []       _        _          = tt
    aux''' (j ∷ js) (x , xs) (ih , ihs) = ih , aux''' js xs ihs
    aux'' : (E' : RDesc J) (xs : ⟦ E' ⟧ (μ E)) → All E' (λ _ x → forget O x ≅ forget P x) xs →
            Σ[ hs ∈ Ṡ E' ] Σ[ xs' ∈ Ṗ (next E' hs) (μ D ∘ e) ] Σ[ xs'' ∈ Ṗ (next E' hs) (μ D ∘ e') ]
              Ḣ-decomp E' (flip Ṗ (μ D ∘ e)) (mapFold E E' (ornAlg O) xs) ≡ (hs , xs')    ×
              (hs , xs'') ≡ Ḣ-decomp E' (flip Ṗ (μ D ∘ e')) (mapFold E E' (ornAlg P) xs)  ×  ṖHEq (next E' hs) xs' xs''
    aux'' (ṿ js)   xs       ihs = tt , mapFold-Ṗ E (ornAlg O) js xs , mapFold-Ṗ E (ornAlg P) js xs , refl , refl , aux''' js xs ihs
    aux'' (σ S E') (s , xs) ihs = (_,_ s ** (id ** (id ** (cong (_,_ s ** id) ** (cong (_,_ s ** id) ** id))))) (aux'' (E' s) xs ihs)
    aux' : {D' D'' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P' : ROrn e' D'' E') → D' ≡ D'' → ROrnEq O' P' →
           (xs : ⟦ E' ⟧ (μ E)) → All E' (λ _ x → forget O x ≅ forget P x) xs →
           ḢTrans-app (ḢTrans-normal O') erase-Ṗ (mapFold E E' (ornAlg O) xs) ≅ ḢTrans-app (ḢTrans-normal P') erase-Ṗ (mapFold E E' (ornAlg P) xs)
    aux' {._} {D'} {E'} O' P' refl roeq xs ihs =
      let (hs , xs' , xs'' , eq , eq' , heq) = aux'' E' xs ihs
      in  ≡-to-≅ (cong (Ḣ-comp D' (flip Ṗ (μ D)))
                       (trans (cong (ḢTrans-app' (ḢTrans-normal O') erase-Ṗ) eq)
                              (trans (cong-ḢTrans-app'-erase-Ṗ (ḢTrans-normal O') (ḢTrans-normal P') eeq (≅-to-≡ ∘ roeq) hs xs' xs'' heq)
                                     (cong (ḢTrans-app' (ḢTrans-normal P') erase-Ṗ) eq'))))
    aux : (j : J) (xs : Ḟ E (μ E) j) → All (Desc.comp E j) (λ _ x → forget O x ≅ forget P x) xs →
          {i : I} (eq : e j ≡ i) {i' : I} (eq' : e' j ≡ i') →
          con {D = D} (subst (Ḟ D (μ D)) eq (erase (Orn.comp O (ok j)) (mapFold E (Desc.comp E j) (ornAlg O) xs)))
            ≅ con {D = D} (subst (Ḟ D (μ D)) eq' (erase (Orn.comp P (ok j)) (mapFold E (Desc.comp E j) (ornAlg P) xs)))
    aux j xs ihs eq eq'  with trans (trans (sym eq) (eeq j)) eq'
    aux j xs ihs eq refl | refl =
      hcong con (htrans (≡-subst-removable (Ḟ D (μ D)) eq (erase (Orn.comp O (ok j)) (mapFold E (Desc.comp E j) (ornAlg O) xs)))
                        (htrans (≡-to-≅ (sym (ḢTrans-app-normal (Orn.comp O (ok j)) erase-Ṗ (mapFold E (Desc.comp E j) (ornAlg O) xs))))
                                (htrans (aux' (Orn.comp O (ok j)) (Orn.comp P (ok j)) (cong (Desc.comp D) (eeq j)) (oeq j) xs ihs)
                                        (≡-to-≅ (ḢTrans-app-normal (Orn.comp P (ok j)) erase-Ṗ (mapFold E (Desc.comp E j) (ornAlg P) xs))))))
