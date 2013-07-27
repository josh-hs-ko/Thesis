-- Parallel composition of ornaments, when mapped to `Fam` by the functor `Ind`, forms a pullback.
-- This file can take a long time to typecheck.

module Ornament.ParallelComposition.Pullback where

open import Prelude.Category
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Equality
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Prelude.Product
open import Description
open import Description.HorizontalEquivalence
open import Ornament
open import Ornament.ParallelComposition
open import Ornament.SequentialComposition
open import Ornament.Equivalence
open import Ornament.Category

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans; proof-irrelevance)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; ≅-to-≡; ≡-to-≅) renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans; proof-irrelevance to hproof-irrelevance)


triangle-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (O ⊙ diffOrn-l O P) ⌈ O ⊗ P ⌉
triangle-l {e = e} {f} O P = (λ { (ok j , k) → refl }) , (λ { (ok j , k) → aux (Orn.comp O (ok j)) (Orn.comp P k) })
  where aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') → ROrnEq (scROrn O' (diffROrn-l O' P')) (toROrn (pcROrn O' P'))
        aux ∎                ∎          X xs           xs'           heq          = ∎
        aux ∎                (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux ∎ (P' t) X xs xs' heq
        aux (ṿ refl)         (ṿ idx')   X xs           xs'           (ṿ heq)      = ṿ heq
        aux (ṿ refl)         (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (ṿ refl) (P' t) X xs xs' heq
        aux (σ S O')         (σ .S P')  X (.s , xs)    (.s , xs')    (σ s heq)    = σ s (aux (O' s) (P' s) X xs xs' heq)
        aux (σ S O')         (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (σ S O') (P' t) X xs xs' heq
        aux (σ S O')         (∇ s P')   X xs           xs'           heq          = σ s (aux (O' s) P' X xs xs' heq)
        aux (Δ T O')         P'         X (.t , xs)    (.t , xs')    (σ t heq)    = aux (O' t) P' X xs xs' heq
        aux (∇ s O')         (σ S P')   X xs           xs'           heq          = σ s (aux O' (P' s) X xs xs' heq)
        aux (∇ {S} s {D} O') (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    =
          subst (λ erase-xs → HoriEq (σ S D) (s , erase-xs) (σ S D) (erase (toROrn (pcROrn (∇ s O') (P' t))) xs'))
                (shiftΔ O' (λ t → diffROrn-l (∇ s O') (P' t)) (t , xs))
                (aux (∇ s O') (P' t)    X xs xs' heq)
        aux (∇ {S} s {D} O') (∇ .s P')  X (.refl , xs) (.refl , xs') (σ refl heq) =
          subst (λ erase-xs → HoriEq (σ S D) (s , erase-xs) (σ S D) (s , erase (toROrn (pcROrn O' P')) xs'))
                (shiftΔ O' (diffROrn-l-double∇ O' P') (refl , xs))
                (σ s (aux O' P' X xs xs' heq))
        aux (O' * O'')       (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (O' * O'') (P' t) X xs xs' heq
        aux (O' * O'')       (P' * P'') X (xs , ys)    (xs' , ys')   (heq * heq') = aux O' P' X xs xs' heq * aux O'' P'' X ys ys' heq'

triangle-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (P ⊙ diffOrn-r O P) ⌈ O ⊗ P ⌉
triangle-r {e = e} {f} O P = (λ { (j , ok k) → refl }) , (λ { (j , ok k) → aux (Orn.comp O j) (Orn.comp P (ok k)) })
  where aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') → ROrnEq (scROrn P' (diffROrn-r O' P')) (toROrn (pcROrn O' P'))
        aux ∎                 ∎          X xs           xs'           heq          = ∎
        aux ∎                 (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux ∎ (P' t) X xs xs' heq
        aux (ṿ idx)           (ṿ refl)   X xs           xs'           (ṿ heq)      = ṿ heq
        aux (ṿ refl)          (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (ṿ refl) (P' t) X xs xs' heq
        aux (σ S O')          (σ .S P')  X (.s , xs)    (.s , xs')    (σ s heq)    = σ s (aux (O' s) (P' s) X xs xs' heq)
        aux (σ S O')          (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (σ S O') (P' t) X xs xs' heq
        aux (σ S O')          (∇ s P')   X xs           xs'           heq          = σ s (aux (O' s) P' X xs xs' heq)
        aux (Δ T {D'} O')     P'         X (.t , xs)    (.t , xs')    (σ t heq)    =
          subst (λ erase-xs → HoriEq D' erase-xs D' (erase (toROrn (pcROrn (O' t) P')) xs'))
                (shiftΔ P' (λ t → diffROrn-r (O' t) P') (t , xs)) (aux (O' t) P' X xs xs' heq)
        aux (∇ s O')          (σ S P')   X xs           xs'           heq          = σ s (aux O' (P' s) X xs xs' heq)
        aux (∇ s O')          (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (∇ s O') (P' t) X xs xs' heq
        aux (∇ {S} s {D'} O') (∇ .s P')  X (.refl , xs) (.refl , xs') (σ refl heq) =
          subst (λ erase-xs → HoriEq (σ S D') (s , erase-xs) (σ S D') (s , erase (toROrn (pcROrn O' P')) xs'))
                (shiftΔ P' (diffROrn-r-double∇ O' P') (refl , xs)) (σ s (aux O' P' X xs xs' heq))
        aux (O' * O'')        (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (O' * O'') (P' t) X xs xs' heq
        aux (O' * O'')        (P' * P'') X (xs , ys)    (xs' , ys')   (heq * heq') = aux O' P' X xs xs' heq * aux O'' P'' X ys ys' heq'

module Integration {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

  integrate-Ind : ∀ {j} → μ E j → Set
  integrate-Ind {j} y = ∀ {k} (z : μ F k) → forget O y ≅ forget P z → ∀ jk → π₁ jk ≡ j → π₂ jk ≡ k →
                        Σ[ p ∶ μ ⌊ O ⊗ P ⌋ jk ] forget (diffOrn-l O P) p ≅ y × forget (diffOrn-r O P) p ≅ z

  integrate-aux₀ :
    ∀ {j} (y : μ E j) → ∀ {k} (z : μ F k) → ∀ {i} (jeq : e j ≡ i) → ∀ {i'} (keq : f k ≡ i') →
    erase (ṿ {e = e} jeq) {μ D} (forget O y) ≅ erase (ṿ {e = f} keq) {μ D} (forget P z) →
    forget O y ≅ forget P z
  integrate-aux₀ y z refl refl eq = eq

  integrate-aux₁ :
    ∀ {i j k} (y : μ E j) (idx : e j ≡ i) (idx' : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ idx , from≡ idx')) →
    forget (diffOrn-l O P) p ≅ y → erase (diffROrn-l (ṿ {e = e} idx) (ṿ {e = f} idx')) {μ E} (forget (diffOrn-l O P) p) ≡ y
  integrate-aux₁ y refl idx' p eq = ≅-to-≡ eq

  integrate-aux₂ :
    ∀ {i j k} (z : μ F k) (idx : e j ≡ i) (idx' : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ idx , from≡ idx')) →
    forget (diffOrn-r O P) p ≅ z → erase (diffROrn-r (ṿ {e = e} idx) (ṿ {e = f} idx')) {μ F} (forget (diffOrn-r O P) p) ≡ z
  integrate-aux₂ z idx refl p eq = ≅-to-≡ eq
  
  integrate-aux :
    ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') →
    (ys : ⟦ E' ⟧ (μ E)) (all : All E' integrate-Ind ys)  (zs : ⟦ F' ⟧ (μ F)) →
    erase O' {μ D} (mapFold E E' (ornAlg O) ys) ≡ erase P' (mapFold F F' (ornAlg P) zs) →
    Σ[ ps ∶ ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋) ]
      erase (diffROrn-l O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps) ≡ ys
    × erase (diffROrn-r O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-r O P) {jk}) ps) ≡ zs
  integrate-aux ∎           ∎            ys         all          zs         eq = tt , refl , refl
  integrate-aux ∎           (Δ T P')     ys         all          (t , zs)   eq =
    (_,_ t ** (id ** cong (_,_ t))) (integrate-aux ∎ (P' t) ys all zs refl)
  integrate-aux (ṿ {j} idx) (ṿ {k} idx') y          all          z          eq =
    let (p , yeq , zeq) = all z (integrate-aux₀ y z idx idx' (≡-to-≅ eq)) (from≡ idx , from≡ idx')
                              (elim-≡ (λ idx  → und (from≡ {f = e} idx ) ≡ j) refl idx )
                              (elim-≡ (λ idx' → und (from≡ {f = f} idx') ≡ k) refl idx')
    in  p , integrate-aux₁ y idx idx' p yeq , integrate-aux₂ z idx idx' p zeq
  integrate-aux (ṿ refl)    (Δ T P')     ys         all          (t , zs)   eq =
    let (ps , yseq , zseq) = integrate-aux (ṿ refl) (P' t) ys all zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (σ S O')    (σ .S P')    ys         all          zs         eq with cong proj₁ eq
  integrate-aux (σ S O')    (σ .S P')    (s , ys)   all          (.s , zs)  eq | refl =
    let (ps , yseq , zseq) = integrate-aux (O' s) (P' s) ys all zs (cong-proj₂ eq) in (s , ps) , cong (_,_ s) yseq , cong (_,_ s) zseq
  integrate-aux (σ S O')    (Δ T P')     ys         all          (t , zs)   eq = 
    let (ps , yseq , zseq) = integrate-aux (σ S O') (P' t) ys all zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (σ S O')    (∇ s P')     ys         all          zs         eq with cong proj₁ eq
  integrate-aux (σ S O')    (∇ s P')     (.s , ys)  all          zs         eq | refl =
    let (ps , yseq , zseq) = integrate-aux (O' s) P' ys all zs (cong-proj₂ eq) in ps , cong (_,_ s) yseq , zseq
  integrate-aux (Δ T O')    P'           (t , ys)   all          zs         eq =
    let (ps , yseq , zseq) = integrate-aux (O' t) P' ys all zs eq in (t , ps) , cong (_,_ t) yseq , zseq
  integrate-aux (∇ s O')    (σ S P')     ys         all          zs eq with cong proj₁ eq
  integrate-aux (∇ s O')    (σ S P')     ys         all          (.s , zs)  eq | refl =
    let (ps , yseq , zseq) = integrate-aux O' (P' s) ys all zs (cong-proj₂ eq) in ps , yseq , cong (_,_ s) zseq
  integrate-aux (∇ s O')    (Δ T P')     ys         all          (t , zs)   eq = 
    let (ps , yseq , zseq) = integrate-aux (∇ s O') (P' t) ys all zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (∇ s O')    (∇ s' P')    ys         all          zs         eq with cong proj₁ eq
  integrate-aux (∇ s O')    (∇ .s P')    ys         all          zs         eq | refl =
    let (ps , yseq , zseq) = integrate-aux O' P' ys all zs (cong-proj₂ eq) in (refl , ps) , yseq , zseq
  integrate-aux (O' * O'')  (Δ T P')     ys         all          (t , zs)   eq =
    let (ps , yseq , zseq) = integrate-aux (O' * O'') (P' t) ys all zs eq in (t , ps) , yseq , cong (_,_ t) zseq
  integrate-aux (O' * O'')  (P' * P'')   (ys , ys') (all , all') (zs , zs') eq =
    let (ps  , yseq  , zseq ) = integrate-aux O'  P'  ys  all  zs  (cong proj₁ eq)
        (ps' , yseq' , zseq') = integrate-aux O'' P'' ys' all' zs' (cong proj₂ eq)
    in  (ps , ps') , cong₂ _,_ yseq yseq' , cong₂ _,_ zseq zseq'
  
  integrate-aux₃ :
    ∀ {i} (j : e ⁻¹ i) {i'} (k : f ⁻¹ i') → i ≡ i' → (ys : ⟦ E at und j ⟧ (μ E)) (zs : ⟦ F at und k ⟧ (μ F)) →
    con {D = D} (erase (Orn.comp O j) (mapFold E (E at und j) (ornAlg O) ys))
      ≅ con {D = D} (erase (Orn.comp P k) (mapFold F (F at und k) (ornAlg P) zs)) →
    erase (Orn.comp O j) {μ D} (mapFold E (E at und j) (ornAlg O) ys)
      ≅ erase (Orn.comp P k) {μ D} (mapFold F (F at und k) (ornAlg P) zs)
  integrate-aux₃ j k refl ys zs eq = ≡-to-≅ (cong decon (≅-to-≡ eq))
  
  integrate-aux₄ :
    ∀ {i} (j : e ⁻¹ i) {i'} (k : f ⁻¹ i') → i ≡ i' → (ys : ⟦ E at und j ⟧ (μ E)) (zs : ⟦ F at und k ⟧ (μ F)) →
    con {D = D} (erase (Orn.comp O (ok (und j))) (mapFold E (E at und j) (ornAlg O) ys))
      ≅ con {D = D} (erase (Orn.comp P (ok (und k))) (mapFold F (F at und k) (ornAlg P) zs)) →
    erase (Orn.comp O j) {μ D} (mapFold E (E at und j) (ornAlg O) ys)
      ≅ erase (Orn.comp P k) {μ D} (mapFold F (F at und k) (ornAlg P) zs)
  integrate-aux₄ (ok j) (ok k) ieq ys zs eq = integrate-aux₃ (ok j) (ok k) ieq ys zs eq
  
  integrate-alg : ∀ {j} (ys : Ḟ E (μ E) j) → All (E at j) integrate-Ind ys → integrate-Ind (con ys)
  integrate-alg ys all (con zs) eq (j , k) refl refl =
    let (ps , yseq , zseq) = integrate-aux (Orn.comp O j) (Orn.comp P k) ys all zs (≅-to-≡ (integrate-aux₄ j k refl ys zs eq))
    in  con ps , ≡-to-≅ (cong con yseq) , ≡-to-≅ (cong con zseq)

  integrate : ∀ {j} (y : μ E j) → integrate-Ind y
  integrate = induction E integrate-Ind integrate-alg

  integrate-inv-Ind : ∀ {jk} → μ ⌊ O ⊗ P ⌋ jk → Set
  integrate-inv-Ind {jk} p =
    (eq : forget O (forget (diffOrn-l O P) p) ≅ forget P (forget (diffOrn-r O P) p)) →
    (jeq : π₁ jk ≡ π₁ jk) (keq : π₂ jk ≡ π₂ jk) →
    proj₁ (integrate (forget (diffOrn-l O P) p) (forget (diffOrn-r O P) p) eq jk jeq keq) ≡ p

  integrate-inv : ∀ {jk} (p : μ ⌊ O ⊗ P ⌋ jk) → integrate-inv-Ind p
  integrate-inv =
    induction ⌊ O ⊗ P ⌋ integrate-inv-Ind (λ { {j , k} ps all eq refl refl → cong con (aux (Orn.comp O j) (Orn.comp P k) ps all _) })
    where
      aux' : ∀ {i k} (j : e ⁻¹ i) (idx : e (und j) ≡ i) (idx' : f k ≡ i)
             (p : μ ⌊ O ⊗ P ⌋ (j , from≡ idx')) (eq : _)
             (all : (eq' : forget O (forget (diffOrn-l O P) p) ≅ forget P (forget (diffOrn-r O P) p)) →
                    (jeq : und j ≡ und j) (keq : und (from≡ {f = f} idx') ≡ und (from≡ {f = f} idx')) →
                    proj₁ (integrate (forget (diffOrn-l O P) p) (forget (diffOrn-r O P) p) eq' (j , from≡ idx') jeq keq) ≡ p) →
             proj₁ (integrate (forget (diffOrn-l O P) p)
                              (erase (diffROrn-r (ṿ {e = e} idx) (ṿ {e = f} idx')) {μ F} (forget (diffOrn-r O P) p))
                              (integrate-aux₀ (forget (diffOrn-l O P) p)
                                              (erase (diffROrn-r (ṿ {e = e} idx) (ṿ {e = f} idx')) {μ F} (forget (diffOrn-r O P) p))
                                              idx idx' eq)
                              (j , from≡ idx') refl (elim-≡ (λ idx'' → und (from≡ {f = f} idx'') ≡ k) refl idx')) ≡ p
      aux' j idx refl p eq all = all _ refl refl
      aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') (ps : ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋))
            (all : All (toRDesc (pcROrn O' P')) integrate-inv-Ind ps) (eq : _) →
            proj₁ (integrate-aux O' P'
                    (erase (diffROrn-l O' P')
                           (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps))
                    (everywhereInduction E E' integrate-Ind integrate-alg
                       (erase (diffROrn-l O' P') 
                              (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps)))
                    (erase (diffROrn-r O' P')
                           (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-r O P) {jk}) ps)) eq) ≡ ps
      aux ∎            ∎          ps          all eq = refl
      aux ∎            (Δ T P')   (t , ps)    all eq = cong (_,_ t) (aux ∎ (P' t) ps all refl)
      aux (ṿ {j} refl) (ṿ idx')   p           all eq = aux' (ok j) refl idx' p _ all
      aux (ṿ refl)     (Δ T P')   (t , ps)    all eq = cong (_,_ t) (aux (ṿ refl) (P' t) ps all eq)
      aux (σ S O')     (σ .S P')  (s , ps)    all eq with cong proj₁ eq
      aux (σ S O')     (σ .S P')  (s , ps)    all eq | refl = cong (_,_ s) (aux (O' s) (P' s) ps all (cong-proj₂ eq))
      aux (σ S O')     (Δ T P')   (t , ps)    all eq = cong (_,_ t) (aux (σ S O') (P' t) ps all eq)
      aux (σ S O')     (∇ s P')   ps          all eq with cong proj₁ eq
      aux (σ S O')     (∇ s P')   ps          all eq | refl = aux (O' s) P' ps all (cong-proj₂ eq)
      aux (Δ T O')     P'         (t , ps)    all eq = cong (_,_ t) (aux (O' t) P' ps all eq)
      aux (∇ s O')     (σ S P')   ps          all eq with cong proj₁ eq
      aux (∇ s O')     (σ S P')   ps          all eq | refl = aux O' (P' s) ps all (cong-proj₂ eq)
      aux (∇ s O')     (Δ T P')   (t , ps)    all eq = cong (_,_ t) (aux (∇ s O') (P' t) ps all eq)
      aux (∇ s O')     (∇ s' P')  ps          all eq with cong proj₁ eq
      aux (∇ s O')     (∇ .s P')  (refl , ps) all eq | refl = cong (_,_ refl) (aux O' P' ps all (cong-proj₂ eq))
      aux (O' * O'')   (Δ T P')   (t , ps)    all eq = cong (_,_ t) (aux (O' * O'') (P' t) ps all eq)
      aux (O' * O'')   (P' * P'') (ps , ps')  (all , all') eq = cong₂ _,_ (aux O' P' ps all (cong proj₁ eq)) (aux O'' P'' ps' all' (cong proj₂ eq))

module IsPullback {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

  open Category
  open Functor

  l : Slice Fam (object Ind (I , D))
  l = slice (object Ind (J , E)) (morphism Ind (e , O))

  r : Slice Fam (object Ind (I , D))
  r = slice (object Ind (K , F)) (morphism Ind (f , P))

  p : Slice Fam (object Ind (I , D))
  p = slice (object Ind (e ⋈ f , ⌊ O ⊗ P ⌋)) (morphism Ind (pull , ⌈ O ⊗ P ⌉))
  
  ⋈-span : Span (SliceCategory Fun I) (slice J e) (slice K f)
  ⋈-span = proj₁ (proj₁ (⋈-is-Pullback e f))

  p-to-l : SliceMorphism Fam (object Ind (I , D)) p l
  p-to-l = sliceMorphism (π₁ , forget (diffOrn-l O P))
                         (SliceMorphism.triangle (Span.l ⋈-span) ,
                          ≑-trans refl (≑-sym (≐-to-≑ (forget-after-forget O (diffOrn-l O P))))
                                       (pointwise (OrnEq-forget (O ⊙ diffOrn-l O P) ⌈ O ⊗ P ⌉ (triangle-l O P))))

  p-to-r : SliceMorphism Fam (object Ind (I , D)) p r
  p-to-r = sliceMorphism (π₂ , forget (diffOrn-r O P))
                         (SliceMorphism.triangle (Span.r ⋈-span) ,
                          ≑-trans refl (≑-sym (≐-to-≑ (forget-after-forget P (diffOrn-r O P))))
                                       (pointwise (OrnEq-forget (P ⊙ diffOrn-r O P) ⌈ O ⊗ P ⌉ (triangle-r O P))))

  module Universality (p' : Slice Fam (object Ind (I , D)))
                      (p'-to-l : SliceMorphism Fam (object Ind (I , D)) p' l)
                      (p'-to-r : SliceMorphism Fam (object Ind (I , D)) p' r) where

    L : Set
    L = proj₁ (Slice.T p')

    g : L → I
    g = FamMorphism.e (Slice.s p')

    L-span : Span (SliceCategory Fun I) (slice J e) (slice K f)
    L-span = object (SpanMap (SliceMap FamI)) (span p' p'-to-l p'-to-r)

    L-to-⋈ : SpanMorphism (SliceCategory Fun I) (slice J e) (slice K f) L-span ⋈-span
    L-to-⋈ = proj₁ (proj₂ (⋈-is-Pullback e f) L-span)

    integrate :
      {i : L} → (t : proj₂ (Slice.T p') i) →
      Σ[ q ∶ μ ⌊ O ⊗ P ⌋ (from≡ (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i) ,
                         from≡ (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i)) ]
         forget (diffOrn-l O P) q ≅ FamMorphism.u (SliceMorphism.m p'-to-l) t ×
         forget (diffOrn-r O P) q ≅ FamMorphism.u (SliceMorphism.m p'-to-r) t
    integrate {i} t = Integration.integrate O P
                        (FamMorphism.u (SliceMorphism.m p'-to-l) t)
                        (FamMorphism.u (SliceMorphism.m p'-to-r) t)
                        (htrans (FamMorphismEq.u (SliceMorphism.triangle p'-to-l) t t hrefl)
                                (hsym (FamMorphismEq.u (SliceMorphism.triangle p'-to-r) t t hrefl)))
                        _
                        (und-from≡ {f = e} (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                        (und-from≡ {f = f} (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))

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
                      ((λ t → und-from≡ {f = e} (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) t)) ,
                       pointwise (λ t → proj₁ (proj₂ (integrate t)))) ⟩
               (e ∘ FamMorphism.e (SliceMorphism.m p'-to-l) , forget O ∘ FamMorphism.u (SliceMorphism.m p'-to-l))
                 ≈⟨ SliceMorphism.triangle p'-to-l ⟩
               Slice.s p'
             □)
      where setoid = Morphism Fam (Slice.T p') (object Ind (I , D))
            open EqReasoning setoid renaming (_∎ to _□)

    p'-to-p : SpanMorphism (SliceCategory Fam (object Ind (I , D))) l r (span p' p'-to-l p'-to-r) (span p p-to-l p-to-r)
    p'-to-p = spanMorphism med
                ((λ t → und-from≡ {f = e} (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) t)) , pointwise (λ t → proj₁ (proj₂ (integrate t))))
                ((λ t → und-from≡ {f = f} (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) t)) , pointwise (λ t → proj₂ (proj₂ (integrate t))))

    uniqueness : Unique (Morphism (SpanCategory (SliceCategory Fam (object Ind (I , D))) l r)
                                  (span p' p'-to-l p'-to-r) (span p p-to-l p-to-r))
                        p'-to-p
    uniqueness med' =
      proj₂ (proj₂ (⋈-is-Pullback e f) L-span)
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
                 (from≡ (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i) , from≡ (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                 (trans (und-from≡ {f = e} (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                        (sym (FamMorphismEq.e (SpanMorphism.triangle-l med') i)))
                 (trans (und-from≡ {f = f} (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                        (sym (FamMorphismEq.e (SpanMorphism.triangle-r med') i)))
                 (FamMorphism.u (SliceMorphism.m p'-to-l) t) (FamMorphism.u (SliceMorphism.m p'-to-r) t)
                 (htrans (FamMorphismEq.u (SliceMorphism.triangle p'-to-l) t t hrefl)
                         (hsym (FamMorphismEq.u (SliceMorphism.triangle p'-to-r) t t hrefl)))
                 (und-from≡ {f = e} (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i))
                 (und-from≡ {f = f} (FamMorphismEq.e (SliceMorphism.triangle p'-to-r) i))
                 (FamMorphismEq.u (SpanMorphism.triangle-l med') t t hrefl)
                 (FamMorphismEq.u (SpanMorphism.triangle-r med') t t hrefl))
               (htrans (cong-integrate' (forget (diffOrn-l O P) w) (forget (diffOrn-r O P) w) _ _ _ _
                                        (FamMorphism.e (SliceMorphism.m (SpanMorphism.m med')) i) refl refl)
                       (≡-to-≅ (Integration.integrate-inv O P _ _ _ _)))))

  ⊗-is-Pullback : Pullback Fam l r (object Ind (e ⋈ f , ⌊ O ⊗ P ⌋))
  ⊗-is-Pullback = (span p p-to-l p-to-r , refl) ,
                  λ { (span p' l' r') → Universality.p'-to-p p' l' r' , Universality.uniqueness p' l' r' }

open IsPullback public using (⊗-is-Pullback)
