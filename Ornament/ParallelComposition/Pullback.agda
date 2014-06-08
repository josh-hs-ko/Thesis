-- Parallel composition of ornaments gives rise to a pullback square in `Ōrn`, which is also a pullback when mapped to `Fam` by the functor `Ind`.
-- This file can take a long time to typecheck.

module Ornament.ParallelComposition.Pullback where

open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Prelude.Product
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.Horizontal.Category
open import Ornament.Horizontal.Pullback
open import Ornament.ParallelComposition
open import Ornament.SequentialComposition
open import Ornament.Equivalence
open import Ornament.Category

open import Function using (id; _∘_; const; _∋_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans; proof-irrelevance)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡; ≡-to-≅; ≡-subst-removable)
                                                  renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans; proof-irrelevance to hproof-irrelevance)

open Functor


Ṡ-pcROrn-decomp : {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K}
                  (O : ROrn e D E) (P : ROrn f D F) → Ṡ (toRDesc (pcROrn O P)) → Σ[ hs ∈ Ṡ E × Ṡ F ] erase-Ṡ O (proj₁ hs) ≡ erase-Ṡ P (proj₂ hs)
Ṡ-pcROrn-decomp (ṿ eqs) (ṿ eqs') h          = (tt , tt) , refl
Ṡ-pcROrn-decomp (ṿ eqs) (Δ T P)  (t , h)    = ((id    ** _,_ t) ** id          ) (Ṡ-pcROrn-decomp (ṿ eqs) (P t) h)
Ṡ-pcROrn-decomp (σ S O) (σ .S P) (s , h)    = ((_,_ s ** _,_ s) ** cong (_,_ s)) (Ṡ-pcROrn-decomp (O s) (P s) h)
Ṡ-pcROrn-decomp (σ S O) (Δ T P)  (t , h)    = ((id    ** _,_ t) ** id          ) (Ṡ-pcROrn-decomp (σ S O) (P t) h)
Ṡ-pcROrn-decomp (σ S O) (∇ s P)  h          = ((_,_ s ** id   ) ** cong (_,_ s)) (Ṡ-pcROrn-decomp (O s) P h)
Ṡ-pcROrn-decomp (Δ T O) P        (t , h)    = ((_,_ t ** id   ) ** id          ) (Ṡ-pcROrn-decomp (O t) P h)
Ṡ-pcROrn-decomp (∇ s O) (σ S P)  h          = ((id    ** _,_ s) ** cong (_,_ s)) (Ṡ-pcROrn-decomp O (P s) h)
Ṡ-pcROrn-decomp (∇ s O) (Δ T P)  (t , h)    = ((id    ** _,_ t) ** id          ) (Ṡ-pcROrn-decomp (∇ s O) (P t) h)
Ṡ-pcROrn-decomp (∇ s O) (∇ .s P) (refl , h) = ((id    ** id   ) ** cong (_,_ s)) (Ṡ-pcROrn-decomp O P h)

Ṡ-pcROrn-comp : {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K}
                (O : ROrn e D E) (P : ROrn f D F) → Σ[ hs ∈ Ṡ E × Ṡ F ] erase-Ṡ O (proj₁ hs) ≡ erase-Ṡ P (proj₂ hs) → Ṡ (toRDesc (pcROrn O P))
Ṡ-pcROrn-comp (ṿ eqs) (ṿ eqs') ((h        , h'       ) , eq) = tt
Ṡ-pcROrn-comp (ṿ eqs) (Δ T P)  ((h        , (t , h') ) , eq) = t , Ṡ-pcROrn-comp (ṿ eqs) (P t) ((h , h') , eq)
Ṡ-pcROrn-comp (σ S O) (σ .S P) (((s , h)  , (s' , h')) , eq) with cong proj₁ eq
Ṡ-pcROrn-comp (σ S O) (σ .S P) (((s , h)  , (.s , h')) , eq) | refl = s , Ṡ-pcROrn-comp (O s) (P s) ((h , h') , cong-proj₂ eq)
Ṡ-pcROrn-comp (σ S O) (Δ T P)  ((h        , (t , h') ) , eq) = t , Ṡ-pcROrn-comp (σ S O) (P t) ((h , h') , eq)
Ṡ-pcROrn-comp (σ S O) (∇ s P)  (((s' , h) , h'       ) , eq) with cong proj₁ eq
Ṡ-pcROrn-comp (σ S O) (∇ s P)  (((.s , h) , h'       ) , eq) | refl = Ṡ-pcROrn-comp (O s) P ((h , h') , cong-proj₂ eq)
Ṡ-pcROrn-comp (Δ T O) P        (((t , h)  , h'       ) , eq) = t , Ṡ-pcROrn-comp (O t) P ((h , h') , eq)
Ṡ-pcROrn-comp (∇ s O) (σ S P)  ((h        , (s' , h')) , eq) with cong proj₁ eq
Ṡ-pcROrn-comp (∇ s O) (σ S P)  ((h        , (.s , h')) , eq) | refl = Ṡ-pcROrn-comp O (P s) ((h , h') , cong-proj₂ eq)
Ṡ-pcROrn-comp (∇ s O) (Δ T P)  ((h        , (t , h') ) , eq) = t , Ṡ-pcROrn-comp (∇ s O) (P t) ((h , h') , eq)
Ṡ-pcROrn-comp (∇ s O) (∇ s' P) ((h        , h'       ) , eq) with cong proj₁ eq
Ṡ-pcROrn-comp (∇ s O) (∇ .s P) ((h        , h'       ) , eq) | refl = refl , Ṡ-pcROrn-comp O P ((h , h') , cong-proj₂ eq)

Ṡ-pcROrn-decomp-comp-inverse :
  {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K}
  (O : ROrn e D E) (P : ROrn f D F) (hs : Σ[ hs ∈ Ṡ E × Ṡ F ] erase-Ṡ O (proj₁ hs) ≡ erase-Ṡ P (proj₂ hs)) →
  proj₁ (Ṡ-pcROrn-decomp O P (Ṡ-pcROrn-comp O P hs)) ≡ proj₁ hs
Ṡ-pcROrn-decomp-comp-inverse (ṿ eqs) (ṿ eqs') ((h        , h'       ) , eq) = refl
Ṡ-pcROrn-decomp-comp-inverse (ṿ eqs) (Δ T P)  ((h        , (t , h') ) , eq) = cong (id ** _,_ t) (Ṡ-pcROrn-decomp-comp-inverse (ṿ eqs) (P t) ((h , h') , eq))
Ṡ-pcROrn-decomp-comp-inverse (σ S O) (σ .S P) (((s , h)  , (s' , h')) , eq) with cong proj₁ eq
Ṡ-pcROrn-decomp-comp-inverse (σ S O) (σ .S P) (((s , h)  , (.s , h')) , eq) | refl = cong (_,_ s ** _,_ s)
                                                                                          (Ṡ-pcROrn-decomp-comp-inverse (O s) (P s) ((h , h') , cong-proj₂ eq))
Ṡ-pcROrn-decomp-comp-inverse (σ S O) (Δ T P)  ((h        , (t , h') ) , eq) = cong (id ** _,_ t) (Ṡ-pcROrn-decomp-comp-inverse (σ S O) (P t) ((h , h') , eq))
Ṡ-pcROrn-decomp-comp-inverse (σ S O) (∇ s P)  (((s' , h) , h'       ) , eq) with cong proj₁ eq
Ṡ-pcROrn-decomp-comp-inverse (σ S O) (∇ s P)  (((.s , h) , h'       ) , eq) | refl = cong (_,_ s ** id) (Ṡ-pcROrn-decomp-comp-inverse (O s) P ((h , h') , cong-proj₂ eq))
Ṡ-pcROrn-decomp-comp-inverse (Δ T O) P        (((t , h)  , h'       ) , eq) = cong (_,_ t ** id) (Ṡ-pcROrn-decomp-comp-inverse (O t) P ((h , h') , eq))
Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (σ S P)  ((h        , (s' , h')) , eq) with cong proj₁ eq
Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (σ S P)  ((h        , (.s , h')) , eq) | refl = cong (id ** _,_ s) (Ṡ-pcROrn-decomp-comp-inverse O (P s) ((h , h') , cong-proj₂ eq))
Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (Δ T P)  ((h        , (t , h') ) , eq) = cong (id ** _,_ t) (Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (P t) ((h , h') , eq))
Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (∇ s' P) ((h        , h'       ) , eq) with cong proj₁ eq
Ṡ-pcROrn-decomp-comp-inverse (∇ s O) (∇ .s P) ((h        , h'       ) , eq) | refl = Ṡ-pcROrn-decomp-comp-inverse O P ((h , h') , cong-proj₂ eq)

Ṡ-pcROrn-comp-decomp-inverse :
  {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K}
  (O : ROrn e D E) (P : ROrn f D F) (h : Ṡ (toRDesc (pcROrn O P))) →
  let ((h' , h'') , _) = Ṡ-pcROrn-decomp O P h in (eq : erase-Ṡ O h' ≡ erase-Ṡ P h'') → Ṡ-pcROrn-comp O P ((h' , h'') , eq) ≡ h
Ṡ-pcROrn-comp-decomp-inverse (ṿ eqs) (ṿ eqs') h          eq = refl
Ṡ-pcROrn-comp-decomp-inverse (ṿ eqs) (Δ T P)  (t , h)    eq = cong (_,_ t) (Ṡ-pcROrn-comp-decomp-inverse (ṿ eqs) (P t) h eq)
Ṡ-pcROrn-comp-decomp-inverse (σ S O) (σ .S P) (s , h)    eq with cong proj₁ eq 
Ṡ-pcROrn-comp-decomp-inverse (σ S O) (σ .S P) (s , h)    eq | refl = cong (_,_ s) (Ṡ-pcROrn-comp-decomp-inverse (O s) (P s) h (cong-proj₂ eq))
Ṡ-pcROrn-comp-decomp-inverse (σ S O) (Δ T P)  (t , h)    eq = cong (_,_ t) (Ṡ-pcROrn-comp-decomp-inverse (σ S O) (P t) h eq)
Ṡ-pcROrn-comp-decomp-inverse (σ S O) (∇ s P)  h          eq with cong proj₁ eq
Ṡ-pcROrn-comp-decomp-inverse (σ S O) (∇ s P)  h          eq | refl = Ṡ-pcROrn-comp-decomp-inverse (O s) P h (cong-proj₂ eq)
Ṡ-pcROrn-comp-decomp-inverse (Δ T O) P        (t , h)    eq = cong (_,_ t) (Ṡ-pcROrn-comp-decomp-inverse (O t) P h eq)
Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (σ S P)  h          eq with cong proj₁ eq
Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (σ S P)  h          eq | refl = Ṡ-pcROrn-comp-decomp-inverse O (P s) h (cong-proj₂ eq)
Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (Δ T P)  (t , h)    eq = cong (_,_ t) (Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (P t) h eq)
Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (∇ .s P) (refl , h) eq with cong proj₁ eq 
Ṡ-pcROrn-comp-decomp-inverse (∇ s O) (∇ .s P) (refl , h) eq | refl = cong (_,_ refl) (Ṡ-pcROrn-comp-decomp-inverse O P h (cong-proj₂ eq))

Ṡ-pcROrn-iso : {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K}
               (O : ROrn e D E) (P : ROrn f D F) → Iso Fun (Ṡ (toRDesc (pcROrn O P))) (Σ[ hs ∈ Ṡ E × Ṡ F ] erase-Ṡ O (proj₁ hs) ≡ erase-Ṡ P (proj₂ hs))
Ṡ-pcROrn-iso O P = record
  { to   = Ṡ-pcROrn-decomp O P
  ; from = Ṡ-pcROrn-comp O P
  ; from-to-inverse = λ h → Ṡ-pcROrn-comp-decomp-inverse O P h (proj₂ (Ṡ-pcROrn-decomp O P h))
  ; to-from-inverse = λ hs → cong₂-pair (Ṡ-pcROrn-decomp-comp-inverse O P hs)
                                        (htrans (≡-to-≅ (proof-irrelevance _ _))
                                                (≡-subst-removable (λ hs' → erase-Ṡ O (proj₁ hs') ≡ erase-Ṡ P (proj₂ hs'))
                                                                   (sym (Ṡ-pcROrn-decomp-comp-inverse O P hs))
                                                                   (proj₂ hs))) }

med-triangle-l : {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K} (O : ROrn e D E) (P : ROrn f D F) →
                 erase-Ṡ (diffROrn-l O P) ≐ proj₁ ∘ proj₁ ∘ Iso.to (Ṡ-pcROrn-iso O P)
med-triangle-l (ṿ eqs) (ṿ eqs') h          = refl
med-triangle-l (ṿ eqs) (Δ T O)  (t , h)    = med-triangle-l (ṿ eqs) (O t) h
med-triangle-l (σ S O) (σ .S P) (s , h)    = cong (_,_ s) (med-triangle-l (O s) (P s) h)
med-triangle-l (σ S O) (Δ T P)  (t , h)    = med-triangle-l (σ S O) (P t) h
med-triangle-l (σ S O) (∇ s P)  h          = cong (_,_ s) (med-triangle-l (O s) P h)
med-triangle-l (Δ T O) P        (t , h)    = cong (_,_ t) (med-triangle-l (O t) P h)
med-triangle-l (∇ s O) (σ S P)  h          = med-triangle-l O (P s) h
med-triangle-l (∇ s O) (Δ T P)  (t , h)    = med-triangle-l (∇ s O) (P t) h
med-triangle-l (∇ s O) (∇ .s P) (refl , h) = med-triangle-l O P h

med-triangle-r : {I J K : Set} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K} (O : ROrn e D E) (P : ROrn f D F) →
                 erase-Ṡ (diffROrn-r O P) ≐ proj₂ ∘ proj₁ ∘ Iso.to (Ṡ-pcROrn-iso O P)
med-triangle-r (ṿ eqs) (ṿ eqs') h          = refl
med-triangle-r (ṿ eqs) (Δ T O)  (t , h)    = cong (_,_ t) (med-triangle-r (ṿ eqs) (O t) h)
med-triangle-r (σ S O) (σ .S P) (s , h)    = cong (_,_ s) (med-triangle-r (O s) (P s) h)
med-triangle-r (σ S O) (Δ T P)  (t , h)    = cong (_,_ t) (med-triangle-r (σ S O) (P t) h)
med-triangle-r (σ S O) (∇ s P)  h          = med-triangle-r (O s) P h
med-triangle-r (Δ T O) P        (t , h)    = med-triangle-r (O t) P h
med-triangle-r (∇ s O) (σ S P)  h          = cong (_,_ s) (med-triangle-r O (P s) h)
med-triangle-r (∇ s O) (Δ T P)  (t , h)    = cong (_,_ t) (med-triangle-r (∇ s O) (P t) h)
med-triangle-r (∇ s O) (∇ .s P) (refl , h) = med-triangle-r O P h

triangle-l' : {I J K : Set} {e : J → I} {f : K → I} {D' : RDesc I} {E' : RDesc J} {F' : RDesc K} (O' : ROrn e D' E') (P' : ROrn f D' F') →
              erase-Ṡ (scROrn O' (diffROrn-l O' P')) ≐ erase-Ṡ (toROrn (pcROrn O' P'))
triangle-l' (ṿ eeqs) (ṿ feqs)  _           = refl
triangle-l' (ṿ eeqs) (Δ T P')  (t , hs)    = triangle-l' (ṿ eeqs) (P' t) hs
triangle-l' (σ S O') (σ .S P') (s , hs)    = cong (_,_ s) (triangle-l' (O' s) (P' s) hs)
triangle-l' (σ S O') (Δ T P')  (t , hs)    = triangle-l' (σ S O') (P' t) hs
triangle-l' (σ S O') (∇ s P')  hs          = cong (_,_ s) (triangle-l' (O' s) P' hs)
triangle-l' (Δ T O') P'        (t , hs)    = triangle-l' (O' t) P' hs
triangle-l' (∇ s O') (σ S P')  hs          = cong (_,_ s) (triangle-l' O' (P' s) hs)
triangle-l' (∇ s O') (Δ T P')  (t , hs)    = trans (cong (_,_ s) (shift-Δ O' (λ t → diffROrn-l (∇ s O') (P' t)) (const !) (t , hs)))
                                                   (triangle-l' (∇ s O') (P' t) hs)
triangle-l' (∇ s O') (∇ .s P') (refl , hs) = cong (_,_ s) (trans (shift-Δ O' (diffROrn-l-double∇ O' P') (const !) (refl , hs)) (triangle-l' O' P' hs))

triangle-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (O ⊙ diffOrn-l O P) ⌈ O ⊗ P ⌉
triangle-l {I} {J} {K} {e} {f} O P = SliceMorphism.triangle (Span.l (⋈-square e f)) ,
                                     λ { (ok j , k) hs → ≡-to-≅ (triangle-l' (Orn.comp O (ok j)) (Orn.comp P k) hs) }

triangle-r' : {I J K : Set} {e : J → I} {f : K → I} {D' : RDesc I} {E' : RDesc J} {F' : RDesc K} (O' : ROrn e D' E') (P' : ROrn f D' F') →
              erase-Ṡ (scROrn P' (diffROrn-r O' P')) ≐ erase-Ṡ (toROrn (pcROrn O' P'))
triangle-r' (ṿ eeqs) (ṿ feqs)  _           = refl
triangle-r' (ṿ eeqs) (Δ T P')  (t , hs)    = triangle-r' (ṿ eeqs) (P' t) hs
triangle-r' (σ S O') (σ .S P') (s , hs)    = cong (_,_ s) (triangle-r' (O' s) (P' s) hs)
triangle-r' (σ S O') (Δ T P')  (t , hs)    = triangle-r' (σ S O') (P' t) hs
triangle-r' (σ S O') (∇ s P')  hs          = cong (_,_ s) (triangle-r' (O' s) P' hs)
triangle-r' (Δ T O') P'        (t , hs)    = trans (shift-Δ P' (λ t → diffROrn-r (O' t) P') (const !) (t , hs)) (triangle-r' (O' t) P' hs)
triangle-r' (∇ s O') (σ S P')  hs          = cong (_,_ s) (triangle-r' O' (P' s) hs)
triangle-r' (∇ s O') (Δ T P')  (t , hs)    = triangle-r' (∇ s O') (P' t) hs
triangle-r' (∇ s O') (∇ .s P') (refl , hs) = cong (_,_ s) (trans (shift-Δ P' (diffROrn-r-double∇ O' P') (const !) (refl , hs)) (triangle-r' O' P' hs))

triangle-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (P ⊙ diffOrn-r O P) ⌈ O ⊗ P ⌉
triangle-r {I} {J} {K} {e} {f} O P = SliceMorphism.triangle (Span.r (⋈-square e f)) ,
                                     λ { (j , ok k) hs → ≡-to-≅ (triangle-r' (Orn.comp O j) (Orn.comp P (ok k)) hs) }

Ōrn-slice : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} → Orn e D E → Slice Ōrn (I , D)
Ōrn-slice {I} {J} {e} {D} {E} O = slice (J , E) (e , O)

erase-Ṡ-ok-und : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) {i : I} (j : e ⁻¹ i) (h : Ṡ (Desc.comp E (und j))) →
                 erase-Ṡ (Orn.comp O (ok (und j))) h ≅ erase-Ṡ (Orn.comp O j) h
erase-Ṡ-ok-und O (ok j) h = hrefl

module PullbackInŌrn {I J K : Set} {e : J → I} {f : K → I} {D : Desc I} {E : Desc J} {F : Desc K} (O : Orn e D E) (P  : Orn f D F) where

  Ōrn-square : Square Ōrn (Ōrn-slice O) (Ōrn-slice P)
  Ōrn-square = span (slice (e ⋈ f , ⌊ O ⊗ P ⌋) (pull , ⌈ O ⊗ P ⌉))
                    (sliceMorphism (π₁ , diffOrn-l O P) (triangle-l O P))
                    (sliceMorphism (π₂ , diffOrn-r O P) (triangle-r O P))
  
  iso-in-Fam-to : {F' : RDesc K} {i : I} (P' : ROrn f (Desc.comp D i) F') {j : J} (jkeq : e j ≡ i)
                  (h : Ṡ (Desc.comp E j)) (h' : Ṡ F') → erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ P' h' → Ṡ (toRDesc (pcROrn (Orn.comp O (from≡ e jkeq)) P'))
  iso-in-Fam-to P' {j} refl h h' heq = Iso.from (Ṡ-pcROrn-iso (Orn.comp O (ok j)) P') ((h , h') , ≅-to-≡ heq)

  iso-in-Fam-to-triangle-c :
    {F' : RDesc K} {i : I} (P' : ROrn f (Desc.comp D i) F') {j : J} (jkeq : e j ≡ i)
    (h : Ṡ (Desc.comp E j)) (h' : Ṡ F') (heq : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ P' h') →
    erase-Ṡ (toROrn (pcROrn (Orn.comp O (from≡ e jkeq)) P')) ≐ erase-Ṡ P' ∘ erase-Ṡ (diffROrn-r (Orn.comp O (from≡ e jkeq)) P') →
    erase-Ṡ (toROrn (pcROrn (Orn.comp O (from≡ e jkeq)) P')) (iso-in-Fam-to P' jkeq h h' heq) ≅ erase-Ṡ P' h'
  iso-in-Fam-to-triangle-c P' {j} refl h h' heq eeq =
    let O' = Orn.comp O (ok j)
    in  ≡-to-≅ (trans (eeq (Ṡ-pcROrn-comp O' P' ((h , h') , ≅-to-≡ heq)))
                      (cong (erase-Ṡ P') (trans (med-triangle-r O' P' (Ṡ-pcROrn-comp (Orn.comp O (ok j)) P' ((h , h') , ≅-to-≡ heq)))
                                                (cong (proj₂ ∘ proj₁) (Iso.to-from-inverse (Ṡ-pcROrn-iso O' P') ((h , h') , ≅-to-≡ heq))))))

  iso-in-Fam-to-triangle-l :
    {F' : RDesc K} {i : I} (P' : ROrn f (Desc.comp D i) F') {j : J} (jkeq : e j ≡ i)
    (h : Ṡ (Desc.comp E j)) (h' : Ṡ F') (heq : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ P' h') →
    erase-Ṡ (diffROrn-l (Orn.comp O (from≡ e jkeq)) P') (iso-in-Fam-to P' jkeq h h' heq) ≅ h
  iso-in-Fam-to-triangle-l P' {j} refl h h' heq =
    let O' = Orn.comp O (ok j)
    in  ≡-to-≅ (trans (med-triangle-l O' P' (Ṡ-pcROrn-comp (Orn.comp O (ok j)) P' ((h , h') , ≅-to-≡ heq)))
                      (cong (proj₁ ∘ proj₁) (Iso.to-from-inverse (Ṡ-pcROrn-iso O' P') ((h , h') , ≅-to-≡ heq))))

  iso-in-Fam-to-triangle-r :
    {F' : RDesc K} {i : I} (P' : ROrn f (Desc.comp D i) F') {j : J} (jkeq : e j ≡ i)
    (h : Ṡ (Desc.comp E j)) (h' : Ṡ F') (heq : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ P' h') →
    erase-Ṡ (diffROrn-r (Orn.comp O (from≡ e jkeq)) P') (iso-in-Fam-to P' jkeq h h' heq) ≅ h'
  iso-in-Fam-to-triangle-r P' {j} refl h h' heq =
    let O' = Orn.comp O (ok j)
    in  ≡-to-≅ (trans (med-triangle-r O' P' (Ṡ-pcROrn-comp (Orn.comp O (ok j)) P' ((h , h') , ≅-to-≡ heq)))
                      (cong (proj₂ ∘ proj₁) (Iso.to-from-inverse (Ṡ-pcROrn-iso O' P') ((h , h') , ≅-to-≡ heq))))

  iso-in-Fam-from :
    {i : I} {j : e ⁻¹ i} {k : f ⁻¹ i} (p : Ṡ (toRDesc (pcROrn (Orn.comp O j) (Orn.comp P k)))) →
    Σ[ hs ∈ Ṡ (Desc.comp E (und j)) × Ṡ (Desc.comp F (und k)) ] erase-Ṡ (Orn.comp O (ok (und j))) (proj₁ hs) ≅ erase-Ṡ (Orn.comp P (ok (und k))) (proj₂ hs)
  iso-in-Fam-from {i} {j} {k} p =
    let ((h , h') , heq) = Iso.to (Ṡ-pcROrn-iso (Orn.comp O j) (Orn.comp P k)) p
    in  (h , h') , htrans (erase-Ṡ-ok-und O j (proj₁ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O j) (Orn.comp P k) p))))
                          (htrans (≡-to-≅ heq) (hsym (erase-Ṡ-ok-und P k (proj₂ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O j) (Orn.comp P k) p))))))

  iso-in-Fam-from-to-inverse :
    {F' : RDesc K} {i : I} (P' : ROrn f (Desc.comp D i) F') {j : J} (jkeq : e j ≡ i)
    (h : Ṡ (Desc.comp E j)) (h' : Ṡ F') (heq : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ P' h') →
    ((Σ[ hs ∈ Ṡ (Desc.comp E (und (from≡ e jkeq))) × Ṡ F' ] erase-Ṡ (Orn.comp O (ok (und (from≡ e jkeq)))) (proj₁ hs) ≅ erase-Ṡ P' (proj₂ hs))
      ∋ proj₁ (Ṡ-pcROrn-decomp (Orn.comp O (from≡ e jkeq)) P' (iso-in-Fam-to P' jkeq h h' heq)) ,
        htrans (erase-Ṡ-ok-und O (from≡ e jkeq) (proj₁ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O (from≡ e jkeq)) P' (iso-in-Fam-to P' jkeq h h' heq)))))
               (htrans (≡-to-≅ (proj₂ (Ṡ-pcROrn-decomp (Orn.comp O (from≡ e jkeq)) P' (iso-in-Fam-to P' jkeq h h' heq)))) hrefl))
      ≅ ((Σ[ hs ∈ Ṡ (Desc.comp E j) × Ṡ F' ] erase-Ṡ (Orn.comp O (ok j)) (proj₁ hs) ≅ erase-Ṡ P' (proj₂ hs)) ∋ (h , h') , heq)
  iso-in-Fam-from-to-inverse {F'} P' {j} refl h h' heq =
    ≡-to-≅ (elim-≡ (λ {hs} _ → (proj₁ hs , htrans (≡-to-≅ (proj₂ hs)) hrefl)
                                 ≡ ((Σ[ hs' ∈ Ṡ (Desc.comp E j) × Ṡ F' ] erase-Ṡ (Orn.comp O (ok j)) (proj₁ hs') ≅ erase-Ṡ P' (proj₂ hs'))
                                      ∋ (h , h') , heq))
                   (cong₂-pair refl (≡-to-≅ (hproof-irrelevance (htrans (≡-to-≅ (≅-to-≡ heq)) hrefl) heq)))
                   (sym (Iso.to-from-inverse (Ṡ-pcROrn-iso (Orn.comp O (ok j)) P') ((h , h') , ≅-to-≡ heq))))

  iso-in-Fam-to-ok-und :
    {i : I} {j : J} (k : f ⁻¹ i) (jkeq : e j ≡ f (und k)) (jkeq' : e j ≡ i)
    (h : Ṡ (Desc.comp E j)) (h' : Ṡ (Desc.comp F (und k)))
    (heq : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ (Orn.comp P (ok (und k))) h') (heq' : erase-Ṡ (Orn.comp O (ok j)) h ≅ erase-Ṡ (Orn.comp P k) h') →
    iso-in-Fam-to (Orn.comp P (ok (und k))) jkeq h h' heq ≅ iso-in-Fam-to (Orn.comp P k) jkeq' h h' heq'
  iso-in-Fam-to-ok-und (ok k) jkeq jkeq' h h' heq heq' =
    elim-≡ (λ {jkeq''} _ → iso-in-Fam-to (Orn.comp P (ok k)) jkeq h h' heq ≅ iso-in-Fam-to (Orn.comp P (ok k)) jkeq'' h h' heq')
           (≡-to-≅ (cong (iso-in-Fam-to (Orn.comp P (ok k)) jkeq h h') (hproof-irrelevance heq heq')))
           (proof-irrelevance jkeq jkeq')

  iso-in-Fam : Iso (SquareCategory Fam (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice O)))
                                       (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice P))))
                   (Mix-square (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice O))) (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice P))))
                   (object (SquareMap Shape) (object (SquareMap Erase) Ōrn-square))
  iso-in-Fam = record
    { to   = spanMorphism
               (sliceMorphism (SquareMorphism-m (Iso.to idx-iso) ,
                               λ { {(j , k) , jkeq} ((h , h') , heq) → iso-in-Fam-to (Orn.comp P (ok k)) jkeq h h' heq })
                              (SliceMorphism.triangle (SpanMorphism.m (Iso.to idx-iso)) ,
                               λ { {(j , k) , jkeq} ((h , h') , heq) ._ hrefl →
                                   iso-in-Fam-to-triangle-c (Orn.comp P (ok k)) jkeq h h' heq
                                     (λ h'' → trans (sym (triangle-r' (Orn.comp O (from≡ e jkeq)) (Orn.comp P (ok k)) h''))
                                                    (erase-Ṡ-scROrn (Orn.comp P (ok k)) (diffROrn-r (Orn.comp O (from≡ e jkeq)) (Orn.comp P (ok k))) h'')) }))
               (SpanMorphism.triangle-l (Iso.to idx-iso) ,
                λ { {(j , k) , jkeq} ((h , h') , heq) ._ hrefl → iso-in-Fam-to-triangle-l (Orn.comp P (ok k)) jkeq h h' heq })
               (SpanMorphism.triangle-r (Iso.to idx-iso) ,
                λ { {(j , k) , jkeq} ((h , h') , heq) ._ hrefl → iso-in-Fam-to-triangle-r (Orn.comp P (ok k)) jkeq h h' heq })
    ; from = spanMorphism
               (sliceMorphism (SquareMorphism-m (Iso.from idx-iso) , iso-in-Fam-from)
                              (SliceMorphism.triangle (SpanMorphism.m (Iso.from idx-iso)) ,
                               λ { {j , k} h ._ hrefl →
                                   htrans (erase-Ṡ-ok-und P k (proj₂ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O j) (Orn.comp P k) h))))
                                          (≡-to-≅ (trans (trans (cong (erase-Ṡ (Orn.comp P k)) (sym (med-triangle-r (Orn.comp O j) (Orn.comp P k) h)))
                                                                (sym (erase-Ṡ-scROrn (Orn.comp P k) (diffROrn-r (Orn.comp O j) (Orn.comp P k)) h)))
                                                         (triangle-r' (Orn.comp O j) (Orn.comp P k) h))) }))
               ((SpanMorphism.triangle-l (Iso.from idx-iso)) ,
                λ { {j , k} h ._ hrefl → ≡-to-≅ (sym (med-triangle-l (Orn.comp O j) (Orn.comp P k) h)) })
               ((SpanMorphism.triangle-r (Iso.from idx-iso)) ,
                λ { {j , k} h ._ hrefl → ≡-to-≅ (sym (med-triangle-r (Orn.comp O j) (Orn.comp P k) h)) })
    ; from-to-inverse = Iso.from-to-inverse idx-iso ,
                        λ { {(j , k) , jkeq} ((h , h') , heq) ._ hrefl → iso-in-Fam-from-to-inverse (Orn.comp P (ok k)) jkeq h h' heq }
    ; to-from-inverse = Iso.to-from-inverse idx-iso ,
                        λ { {ok j , k} h ._ hrefl →
                            htrans (iso-in-Fam-to-ok-und k _ refl
                                      (proj₁ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O (ok j)) (Orn.comp P k) h)))
                                      (proj₂ (proj₁ (Ṡ-pcROrn-decomp (Orn.comp O (ok j)) (Orn.comp P k) h))) _
                                      (≡-to-≅ (proj₂ (Ṡ-pcROrn-decomp (Orn.comp O (ok j)) (Orn.comp P k) h))))
                                   (≡-to-≅ (trans (cong (Ṡ-pcROrn-comp (Orn.comp O (ok j)) (Orn.comp P k)) (cong₂-pair refl (≡-to-≅ (proof-irrelevance _ _))))
                                                  (Iso.from-to-inverse (Ṡ-pcROrn-iso (Orn.comp O (ok j)) (Orn.comp P k)) h))) } }
    where idx-iso : Iso (SquareCategory Fun (slice J e) (slice K f)) (STP-square e f) (⋈-square e f)
          idx-iso = terminal-iso (SquareCategory Fun (slice J e) (slice K f)) (STP-square e f) (⋈-square e f) (STP-is-pullback e f) (⋈-is-pullback e f)

  Fam-pullback : Pullback Fam (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice O))) (object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice P)))
                              (object (SquareMap Shape) (object (SquareMap Erase) Ōrn-square))
  Fam-pullback = let s = object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice O))
                     t = object (SliceMap Shape) (object (SliceMap Erase) (Ōrn-slice P))
                 in  iso-terminal (SquareCategory Fam s t) (Mix-square s t) (object (SquareMap Shape) (object (SquareMap Erase) Ōrn-square))
                                                           (canonPullback s t) iso-in-Fam

  ḞḢTrans-pullback : Pullback ḞḢTrans (object (SliceMap Erase) (Ōrn-slice O)) (object (SliceMap Erase) (Ōrn-slice P)) (object (SquareMap Erase) Ōrn-square)
  ḞḢTrans-pullback = Shape-reflects-pullback (object (SliceMap Erase) (Ōrn-slice O)) (object (SliceMap Erase) (Ōrn-slice P))
                                             (object (SquareMap Erase) Ōrn-square) Fam-pullback

  Ōrn-pullback : Pullback Ōrn (Ōrn-slice O) (Ōrn-slice P) Ōrn-square
  Ōrn-pullback = Erase-reflects-pullback (Ōrn-slice O) (Ōrn-slice P) Ōrn-square ḞḢTrans-pullback

module Integration {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

  integrate-Ind : (j : J) → μ E j → Set
  integrate-Ind j y = {k : K} (z : μ F k) → forget O y ≅ forget P z → ∀ jk → π₁ jk ≡ j → π₂ jk ≡ k →
                      Σ[ p ∈ μ ⌊ O ⊗ P ⌋ jk ] forget (diffOrn-l O P) p ≅ y × forget (diffOrn-r O P) p ≅ z

  integrate-aux₀ :
    ∀ {j} (y : μ E j) → ∀ {k} (z : μ F k) → ∀ {i} (eeq : e j ≡ i) → ∀ {i'} (feq : f k ≡ i') → i ≡ i' →
    ∀ {is js ks} (ys : Ṗ js (μ E)) (zs : Ṗ ks (μ F)) (eeqs : Ė e js is) (feqs : Ė f ks is) →
    erase-Ṗ {X = μ D} (eeq ∷ eeqs) (forget O y , mapFold-Ṗ E (ornAlg O) js ys)
      ≅ erase-Ṗ {X = μ D} (feq ∷ feqs) (forget P z , mapFold-Ṗ F (ornAlg P) ks zs) →
    forget O y ≅ forget P z × erase-Ṗ {X = μ D} eeqs (mapFold-Ṗ E (ornAlg O) js ys) ≡ erase-Ṗ {X = μ D} feqs (mapFold-Ṗ F (ornAlg P) ks zs)
  integrate-aux₀ y z refl refl ieq ys zs eeqs feqs eq = (id ** ≅-to-≡) (cong-split (cong (μ D) ieq) refl eq)

  integrate-aux₁ :
    ∀ {i j k} (y : μ E j) (eeq : e j ≡ i) (feq : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ e eeq , from≡ f feq)) → forget (diffOrn-l O P) p ≅ y →
    ∀ {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṗ (und-Ṗ is (pc-Ė eeqs feqs)) (μ ⌊ O ⊗ P ⌋)) →
    {ys : Ṗ js (μ E)} →
    erase-Ṗ (diff-Ė-l eeqs feqs) (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps) ≡ ys →
    erase-Ṗ (_∷_ {j = from≡ e eeq , from≡ f feq} (und-from≡ e eeq) (diff-Ė-l eeqs feqs))
      (forget (diffOrn-l O P) p , mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps) ≡ (y , ys)
  integrate-aux₁ y refl feq p heq eeqs feqs ps eq = cong₂ _,_ (≅-to-≡ heq) eq

  integrate-aux₂ :
    ∀ {i j k} (z : μ F k) (eeq : e j ≡ i) (feq : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ e eeq , from≡ f feq)) → forget (diffOrn-r O P) p ≅ z →
    ∀ {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṗ (und-Ṗ is (pc-Ė eeqs feqs)) (μ ⌊ O ⊗ P ⌋)) →
    {zs : Ṗ ks (μ F)} →
    erase-Ṗ (diff-Ė-r eeqs feqs) (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps) ≡ zs →
    erase-Ṗ (_∷_ {j = from≡ e eeq , from≡ f feq} (und-from≡ f feq) (diff-Ė-r eeqs feqs))
      (forget (diffOrn-r O P) p , mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs))  ps) ≡ (z , zs)
  integrate-aux₂ z eeq refl p heq eeqs feqs ps eq = cong₂ _,_ (≅-to-≡ heq) eq

  integrate-aux-Ṗ :
    {is : List I} {js : List J} {ks : List K}
    (eeqs : Ė e js is) (feqs : Ė f ks is) → (ys : Ṗ js (μ E)) → All-Ṗ integrate-Ind js ys → (zs : Ṗ ks (μ F)) →
    erase-Ṗ {X = μ D} eeqs (mapFold-Ṗ E (ornAlg O) js ys) ≡ erase-Ṗ feqs (mapFold-Ṗ F (ornAlg P) ks zs) →
    Σ[ ps ∈ Ṗ (und-Ṗ is (pc-Ė eeqs feqs)) (μ ⌊ O ⊗ P ⌋) ]
      erase-Ṗ (diff-Ė-l eeqs feqs) (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps) ≡ ys
    × erase-Ṗ (diff-Ė-r eeqs feqs) (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps) ≡ zs
  integrate-aux-Ṗ []           []           _        _          _        _  = tt , refl , refl
  integrate-aux-Ṗ (eeq ∷ eeqs) (feq ∷ feqs) (y , ys) (ih , ihs) (z , zs) eq =
    let (heq , eq') = integrate-aux₀ y z eeq feq refl ys zs eeqs feqs (≡-to-≅ eq)
        (ps , yeqs , zeqs) = integrate-aux-Ṗ eeqs feqs ys ihs zs eq'
        (p  , yeq  , zeq ) = ih z heq _ (und-from≡ e eeq) (und-from≡ f feq)
    in  (p , ps) , integrate-aux₁ y eeq feq p yeq eeqs feqs ps yeqs , integrate-aux₂ z eeq feq p zeq eeqs feqs ps zeqs

  integrate-aux :
    ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') →
    (ys : ⟦ E' ⟧ (μ E)) → All E' integrate-Ind ys → (zs : ⟦ F' ⟧ (μ F)) →
    erase O' {μ D} (mapFold E E' (ornAlg O) ys) ≡ erase P' (mapFold F F' (ornAlg P) zs) →
    Σ[ ps ∈ ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋) ]
      erase (diffROrn-l O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps) ≡ ys
    × erase (diffROrn-r O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-r O P) {jk}) ps) ≡ zs
  integrate-aux (ṿ eeqs)    (ṿ feqs)     ys         ihs          zs         eq = integrate-aux-Ṗ eeqs feqs ys ihs zs eq
  integrate-aux (ṿ eeqs)    (Δ T P')     ys         ihs          (t , zs)   eq =
    let (ps , yseq , zseq) = integrate-aux (ṿ eeqs) (P' t) ys ihs zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (σ S O')    (σ .S P')    ys         ihs          zs         eq with cong proj₁ eq
  integrate-aux (σ S O')    (σ .S P')    (s , ys)   ihs          (.s , zs)  eq | refl =
    let (ps , yseq , zseq) = integrate-aux (O' s) (P' s) ys ihs zs (cong-proj₂ eq) in (s , ps) , cong (_,_ s) yseq , cong (_,_ s) zseq
  integrate-aux (σ S O')    (Δ T P')     ys         ihs          (t , zs)   eq = 
    let (ps , yseq , zseq) = integrate-aux (σ S O') (P' t) ys ihs zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (σ S O')    (∇ s P')     ys         ihs          zs         eq with cong proj₁ eq
  integrate-aux (σ S O')    (∇ s P')     (.s , ys)  ihs          zs         eq | refl =
    let (ps , yseq , zseq) = integrate-aux (O' s) P' ys ihs zs (cong-proj₂ eq) in ps , cong (_,_ s) yseq , zseq
  integrate-aux (Δ T O')    P'           (t , ys)   ihs          zs         eq =
    let (ps , yseq , zseq) = integrate-aux (O' t) P' ys ihs zs eq in (t , ps) , cong (_,_ t) yseq , zseq
  integrate-aux (∇ s O')    (σ S P')     ys         ihs          zs eq with cong proj₁ eq
  integrate-aux (∇ s O')    (σ S P')     ys         ihs          (.s , zs)  eq | refl =
    let (ps , yseq , zseq) = integrate-aux O' (P' s) ys ihs zs (cong-proj₂ eq) in ps , yseq , cong (_,_ s) zseq
  integrate-aux (∇ s O')    (Δ T P')     ys         ihs          (t , zs)   eq = 
    let (ps , yseq , zseq) = integrate-aux (∇ s O') (P' t) ys ihs zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (∇ s O')    (∇ s' P')    ys         ihs          zs         eq with cong proj₁ eq
  integrate-aux (∇ s O')    (∇ .s P')    ys         ihs          zs         eq | refl =
    let (ps , yseq , zseq) = integrate-aux O' P' ys ihs zs (cong-proj₂ eq) in (refl , ps) , yseq , zseq
  
  integrate-aux₃ :
    ∀ {i} (j : e ⁻¹ i) {i'} (k : f ⁻¹ i') → i ≡ i' →
    (ys : ⟦ Desc.comp E (und j) ⟧ (μ E)) (zs : ⟦ Desc.comp F (und k) ⟧ (μ F)) →
    con {D = D} (erase (Orn.comp O j) (mapFold E (Desc.comp E (und j)) (ornAlg O) ys))
      ≅ con {D = D} (erase (Orn.comp P k) (mapFold F (Desc.comp F (und k)) (ornAlg P) zs)) →
    erase (Orn.comp O j) {μ D} (mapFold E (Desc.comp E (und j)) (ornAlg O) ys)
      ≅ erase (Orn.comp P k) {μ D} (mapFold F (Desc.comp F (und k)) (ornAlg P) zs)
  integrate-aux₃ j k refl ys zs eq = ≡-to-≅ (cong decon (≅-to-≡ eq))
  
  integrate-aux₄ :
    ∀ {i} (j : e ⁻¹ i) {i'} (k : f ⁻¹ i') → i ≡ i' →
    (ys : ⟦ Desc.comp E (und j) ⟧ (μ E)) (zs : ⟦ Desc.comp F (und k) ⟧ (μ F)) →
    con {D = D} (erase (Orn.comp O (ok (und j))) (mapFold E (Desc.comp E (und j)) (ornAlg O) ys))
      ≅ con {D = D} (erase (Orn.comp P (ok (und k))) (mapFold F (Desc.comp F (und k)) (ornAlg P) zs)) →
    erase (Orn.comp O j) {μ D} (mapFold E (Desc.comp E (und j)) (ornAlg O) ys)
      ≅ erase (Orn.comp P k) {μ D} (mapFold F (Desc.comp F (und k)) (ornAlg P) zs)
  integrate-aux₄ (ok j) (ok k) ieq ys zs eq = integrate-aux₃ (ok j) (ok k) ieq ys zs eq
  
  integrate-alg : (j : J) (ys : Ḟ E (μ E) j) → All (Desc.comp E j) integrate-Ind ys → integrate-Ind j (con ys)
  integrate-alg ._ ys ihs (con zs) eq (j , k) refl refl =
    let (ps , yseq , zseq) = integrate-aux (Orn.comp O j) (Orn.comp P k) ys ihs zs (≅-to-≡ (integrate-aux₄ j k refl ys zs eq))
    in  con ps , ≡-to-≅ (cong con yseq) , ≡-to-≅ (cong con zseq)

  integrate : ∀ {j} (y : μ E j) → integrate-Ind j y
  integrate = induction E integrate-Ind integrate-alg

  integrate-inv-Ind : (jk : e ⋈ f) → μ ⌊ O ⊗ P ⌋ jk → Set
  integrate-inv-Ind jk p =
    (eq : forget O (forget (diffOrn-l O P) p) ≅ forget P (forget (diffOrn-r O P) p)) →
    (jeq : π₁ jk ≡ π₁ jk) (keq : π₂ jk ≡ π₂ jk) →
    proj₁ (integrate (forget (diffOrn-l O P) p) (forget (diffOrn-r O P) p) eq jk jeq keq) ≡ p

  integrate-inv : ∀ {jk} (p : μ ⌊ O ⊗ P ⌋ jk) → integrate-inv-Ind jk p
  integrate-inv =
    induction ⌊ O ⊗ P ⌋ integrate-inv-Ind (λ { (j , k) ps ihs eq refl refl → cong con (aux (Orn.comp O j) (Orn.comp P k) ps ihs _) })
    where
      aux' : ∀ {i k} (j : e ⁻¹ i) (eeq : e (und j) ≡ i) (feq : f k ≡ i)
             (p : μ ⌊ O ⊗ P ⌋ (j , from≡ f feq)) (ih : integrate-inv-Ind (j , from≡ f feq) p)
             {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṗ (und-Ṗ is (pc-Ė eeqs feqs)) (μ ⌊ O ⊗ P ⌋)) (heq : _) →
             proj₁ (integrate
                      (forget (diffOrn-l O P) p)
                      (subst (μ F) (und-from≡ f feq) (forget (diffOrn-r O P) p))
                      (proj₁ (integrate-aux₀
                                (forget (diffOrn-l O P) p)
                                (subst (μ F) (und-from≡ f feq) (forget (diffOrn-r O P) p))
                                eeq feq refl
                                (erase-Ṗ (diff-Ė-l eeqs feqs)
                                         (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps))
                                (erase-Ṗ (diff-Ė-r eeqs feqs)
                                         (mapFold-Ṗ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṗ is (pc-Ė eeqs feqs)) ps))
                                eeqs feqs heq))
                      (j , from≡ f feq) refl (und-from≡ f feq)) ≡ p
      aux' j eeq refl p ih heq eeqs feqs ps = ih _ refl refl
      aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') (ps : ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋)) →
            All (toRDesc (pcROrn O' P')) integrate-inv-Ind ps → (eq : _) →
            proj₁ (integrate-aux O' P'
                    (erase (diffROrn-l O' P')
                           (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps))
                    (everywhereInduction E E' integrate-Ind integrate-alg
                       (erase (diffROrn-l O' P')
                              (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps)))
                    (erase (diffROrn-r O' P')
                           (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-r O P) {jk}) ps)) eq) ≡ ps
      aux (ṿ [])            (ṿ [])           _           _          _  = refl
      aux (ṿ (refl ∷ eeqs)) (ṿ (feq ∷ feqs)) (p , ps)    (ih , ihs) _  = cong₂ _,_ (aux' (ok _) refl feq p ih eeqs feqs ps _)
                                                                                   (aux (ṿ eeqs) (ṿ feqs) ps ihs _)
      aux (ṿ eeqs)          (Δ T P')         (t , ps)    ihs        eq = cong (_,_ t) (aux (ṿ eeqs) (P' t) ps ihs eq)
      aux (σ S O')          (σ .S P')        (s , ps)    ihs        eq with cong proj₁ eq
      aux (σ S O')          (σ .S P')        (s , ps)    ihs        eq | refl = cong (_,_ s) (aux (O' s) (P' s) ps ihs (cong-proj₂ eq))
      aux (σ S O')          (Δ T P')         (t , ps)    ihs        eq = cong (_,_ t) (aux (σ S O') (P' t) ps ihs eq)
      aux (σ S O')          (∇ s P')         ps          ihs        eq with cong proj₁ eq
      aux (σ S O')          (∇ s P')         ps          ihs        eq | refl = aux (O' s) P' ps ihs (cong-proj₂ eq)
      aux (Δ T O')          P'               (t , ps)    ihs        eq = cong (_,_ t) (aux (O' t) P' ps ihs eq)
      aux (∇ s O')          (σ S P')         ps          ihs        eq with cong proj₁ eq
      aux (∇ s O')          (σ S P')         ps          ihs        eq | refl = aux O' (P' s) ps ihs (cong-proj₂ eq)
      aux (∇ s O')          (Δ T P')         (t , ps)    ihs        eq = cong (_,_ t) (aux (∇ s O') (P' t) ps ihs eq)
      aux (∇ s O')          (∇ s' P')        ps          ihs        eq with cong proj₁ eq
      aux (∇ s O')          (∇ .s P')        (refl , ps) ihs        eq | refl = cong (_,_ refl) (aux O' P' ps ihs (cong-proj₂ eq))

module PullbackInFam {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

  open Category
  open Functor

  l : Slice Fam (object Ind (I , D))
  l = object (SliceMap Ind) (Ōrn-slice O)

  r : Slice Fam (object Ind (I , D))
  r = object (SliceMap Ind) (Ōrn-slice P)

  ⊗-square : Square Fam l r
  ⊗-square = object (SquareMap Ind) (PullbackInŌrn.Ōrn-square O P)

  p : Slice Fam (object Ind (I , D))
  p = Span.M ⊗-square

  p-to-l : SliceMorphism Fam (object Ind (I , D)) p l
  p-to-l = Span.l ⊗-square

  p-to-r : SliceMorphism Fam (object Ind (I , D)) p r
  p-to-r = Span.r ⊗-square

  module Universality (p' : Slice Fam (object Ind (I , D)))
                      (p'-to-l : SliceMorphism Fam (object Ind (I , D)) p' l)
                      (p'-to-r : SliceMorphism Fam (object Ind (I , D)) p' r) where

    L : Set
    L = proj₁ (Slice.T p')

    g : L → I
    g = FamMorphism.e (Slice.s p')

    L-square : Square Fun (slice J e) (slice K f)
    L-square = object (SpanMap (SliceMap FamI)) (span p' p'-to-l p'-to-r)

    L-to-⋈ : SpanMorphism (SliceCategory Fun I) (slice J e) (slice K f) L-square (⋈-square e f)
    L-to-⋈ = proj₁ (⋈-is-pullback e f L-square)

    integrate :
      {i : L} → (t : proj₂ (Slice.T p') i) →
      Σ[ q ∈ μ ⌊ O ⊗ P ⌋ (from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i) ,
                         from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i)) ]
         forget (diffOrn-l O P) q ≅ FamMorphism.u (SliceMorphism.m p'-to-l) t ×
         forget (diffOrn-r O P) q ≅ FamMorphism.u (SliceMorphism.m p'-to-r) t
    integrate {i} t = Integration.integrate O P
                        (FamMorphism.u (SliceMorphism.m p'-to-l) t)
                        (FamMorphism.u (SliceMorphism.m p'-to-r) t)
                        (htrans (FamMorphismEq.u (SliceMorphism.triangle p'-to-l) t t hrefl)
                                (hsym (FamMorphismEq.u (SliceMorphism.triangle p'-to-r) t t hrefl)))
                        _
                        (und-from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                        (und-from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))

    cong-integrate :
      ∀ {j k} (y : μ E j) (z : μ F k) (heq : forget O y ≅ forget P z) (jk : e ⋈ f) (jeq : π₁ jk ≡ j) (keq : π₂ jk ≡ k) →
      ∀ {j' k'} (y' : μ E j') (z' : μ F k') (heq' : forget O y' ≅ forget P z') (jeq' : π₁ jk ≡ j') (keq' : π₂ jk ≡ k') →
      y ≅ y' → z ≅ z' →
      proj₁ (Integration.integrate O P y z heq jk jeq keq) ≡ proj₁ (Integration.integrate O P y' z' heq' jk jeq' keq')
    cong-integrate y z heq jk jeq keq y' z' heq' jeq' keq' yeq zeq
      with trans (sym jeq) jeq' | trans (sym keq) keq'
    cong-integrate y z heq jk jeq keq .y .z heq' jeq' keq' hrefl hrefl | refl | refl
      with proof-irrelevance jeq jeq' | proof-irrelevance keq keq' | hproof-irrelevance heq heq'
    cong-integrate y z heq jk jeq keq .y .z .heq .jeq .keq hrefl hrefl | refl | refl | refl | refl | refl = refl

    cong-integrate' :
      ∀ {j k} (y : μ E j) (z : μ F k) (heq : forget O y ≅ forget P z) (jk : e ⋈ f) (jeq : π₁ jk ≡ j) (keq : π₂ jk ≡ k) →
      (jk' : e ⋈ f) (jeq' : π₁ jk' ≡ j) (keq' : π₂ jk' ≡ k) →
      proj₁ (Integration.integrate O P y z heq jk jeq keq) ≅ proj₁ (Integration.integrate O P y z heq jk' jeq' keq')
    cong-integrate' y z heq jk jeq keq jk' jeq' keq' with decouple {p = jk} {jk'} (trans jeq (sym jeq')) (trans keq (sym keq'))
    cong-integrate' y z heq jk jeq keq .jk jeq' keq' | refl with proof-irrelevance jeq jeq' | proof-irrelevance keq keq'
    cong-integrate' y z heq jk jeq keq .jk .jeq .keq | refl | refl | refl = hrefl

    med : SliceMorphism Fam (object Ind (I , D)) p' p
    med = sliceMorphism
            (SliceMorphism.m (SpanMorphism.m L-to-⋈) , proj₁ ∘ integrate)
            (begin
               (pull ∘ SliceMorphism.m (SpanMorphism.m L-to-⋈) , forget ⌈ O ⊗ P ⌉ ∘ proj₁ ∘ integrate)
                 ≈⟨ Setoid.sym setoid
                      (cong-r Fam (SliceMorphism.m (SpanMorphism.m L-to-⋈) , proj₁ ∘ integrate) (SliceMorphism.triangle p-to-l)) ⟩
               (e ∘ π₁ ∘ SliceMorphism.m (SpanMorphism.m L-to-⋈) , forget O ∘ forget (diffOrn-l O P) ∘ proj₁ ∘ integrate)
                 ≈⟨ cong-l Fam (e , forget O)
                      ((λ t → und-from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) t)) ,
                       pointwise (λ t → proj₁ (proj₂ (integrate t)))) ⟩
               (e ∘ FamMorphism.e (SliceMorphism.m p'-to-l) , forget O ∘ FamMorphism.u (SliceMorphism.m p'-to-l))
                 ≈⟨ SliceMorphism.triangle p'-to-l ⟩
               Slice.s p'
             □)
      where setoid = Morphism Fam (Slice.T p') (object Ind (I , D))
            open EqReasoning setoid renaming (_∎ to _□)

    p'-to-p : SpanMorphism (SliceCategory Fam (object Ind (I , D))) l r (span p' p'-to-l p'-to-r) (span p p-to-l p-to-r)
    p'-to-p = spanMorphism med
                ((λ t → und-from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) t)) , pointwise (λ t → proj₁ (proj₂ (integrate t))))
                ((λ t → und-from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) t)) , pointwise (λ t → proj₂ (proj₂ (integrate t))))

    uniqueness : Unique (Morphism (SpanCategory (SliceCategory Fam (object Ind (I , D))) l r)
                                  (span p' p'-to-l p'-to-r) (span p p-to-l p-to-r))
                        p'-to-p
    uniqueness med' =
      proj₂ (⋈-is-pullback e f L-square)
        (spanMorphism
           (sliceMorphism (FamMorphism.e (SliceMorphism.m (SpanMorphism.m med')))
                          (FamMorphismEq.e (SliceMorphism.triangle (SpanMorphism.m med'))))
           (FamMorphismEq.e (SpanMorphism.triangle-l med'))
           (FamMorphismEq.e (SpanMorphism.triangle-r med'))) ,
      (λ {i} → pointwise (λ t →
         let w = FamMorphism.u (SliceMorphism.m (SpanMorphism.m med')) t
         in  subst (λ w' → w' ≅ w)
               (cong-integrate (forget (diffOrn-l O P) w) (forget (diffOrn-r O P) w)
                 (htrans (FamMorphismEq.u (SliceMorphism.triangle p-to-l) w w hrefl)
                         (hsym (FamMorphismEq.u (SliceMorphism.triangle p-to-r) w w hrefl)))
                 (from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i) , from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                 (trans (und-from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                        (sym (FamMorphismEq.e (SpanMorphism.triangle-l med') i)))
                 (trans (und-from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                        (sym (FamMorphismEq.e (SpanMorphism.triangle-r med') i)))
                 (FamMorphism.u (SliceMorphism.m p'-to-l) t) (FamMorphism.u (SliceMorphism.m p'-to-r) t)
                 (htrans (FamMorphismEq.u (SliceMorphism.triangle p'-to-l) t t hrefl)
                         (hsym (FamMorphismEq.u (SliceMorphism.triangle p'-to-r) t t hrefl)))
                 (und-from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                 (und-from≡ f (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                 (FamMorphismEq.u (SpanMorphism.triangle-l med') t t hrefl)
                 (FamMorphismEq.u (SpanMorphism.triangle-r med') t t hrefl))
               (htrans (cong-integrate' (forget (diffOrn-l O P) w) (forget (diffOrn-r O P) w) _ _ _ _
                                        (FamMorphism.e (SliceMorphism.m (SpanMorphism.m med')) i) refl refl)
                       (≡-to-≅ (Integration.integrate-inv O P _ _ _ _)))))

  ⊗-is-pullback : Pullback Fam l r ⊗-square
  ⊗-is-pullback (span p' l' r') = Universality.p'-to-p p' l' r' , Universality.uniqueness p' l' r'

open PullbackInFam public using () renaming (⊗-square to ⊗-Fam-square; ⊗-is-pullback to ⊗-is-Fam-pullback)

Ind-preserves-pullback : Pullback-preserving Ind
Ind-preserves-pullback =
  particular-pullback-preservation Ind λ { (slice _ (_ , O)) (slice _ (_ , P)) → PullbackInŌrn.Ōrn-square O P ,
                                                                                 PullbackInŌrn.Ōrn-pullback O P , ⊗-is-Fam-pullback O P }
