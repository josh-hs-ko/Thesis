-- Parallel composition of ornaments, when mapped to `Fam` by the functor `Ind`, forms a pullback.
-- This file can take a long time to typecheck.

module Thesis.Ornament.ParallelComposition.Pullback where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Category.Span
open import Thesis.Prelude.Category.Pullback
open import Thesis.Prelude.Equality
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Product
open import Thesis.Description
open import Thesis.Description.HorizontalEquivalence
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.Equivalence
open import Thesis.Ornament.Category

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans; proof-irrelevance)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; ≅-to-≡; ≡-to-≅) renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans; proof-irrelevance to hproof-irrelevance)


triangle-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (O ⊙ diffOrn-l O P) ⌈ O ⊗ P ⌉
triangle-l {I} {J} {K} {e} {f} O P = (λ { (ok j , k) → refl }) , (λ { (ok j , k) → aux (Orn.comp O (ok j)) (Orn.comp P k) })
  where
    aux' : {is : List I} {js : List J} {ks : List K} (eeqs : Ė e js is) (feqs : Ė f ks is)
           (X : I → Set) (xs : Ṁ (X ∘ e ∘ π₁) (und-Ṁ is (pc-Ė eeqs feqs))) (xs' : Ṁ (X ∘ pull) (und-Ṁ is (pc-Ė eeqs feqs))) →
           ṀHEq (und-Ṁ is (pc-Ė eeqs feqs)) xs xs' →
           ṀHEq is (erase-Ṁ (sc-Ė eeqs (diff-Ė-l eeqs feqs)) {X} xs) (erase-Ṁ (to≡-Ṁ is (pc-Ė eeqs feqs)) {X} xs')
    aux' []            _          X _        _          _            = tt
    aux' (refl ∷ eeqs) (_ ∷ feqs) X (x , xs) (x' , xs') (heq , heqs) = heq , aux' eeqs feqs X xs xs' heqs
    aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') → ROrnEq (scROrn O' (diffROrn-l O' P')) (toROrn (pcROrn O' P'))
    aux (ṿ eeqs)         (ṿ feqs)   X xs           xs'           (ṿ heq)      = ṿ (aux' eeqs feqs X xs xs' heq)
    aux (ṿ eeqs)         (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (ṿ eeqs) (P' t) X xs xs' heq
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

triangle-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) → OrnEq (P ⊙ diffOrn-r O P) ⌈ O ⊗ P ⌉
triangle-r {I} {J} {K} {e} {f} O P = (λ { (j , ok k) → refl }) , (λ { (j , ok k) → aux (Orn.comp O j) (Orn.comp P (ok k)) })
  where
    aux' : {is : List I} {js : List J} {ks : List K} (eeqs : Ė e js is) (feqs : Ė f ks is)
           (X : I → Set) (xs : Ṁ (X ∘ f ∘ π₂) (und-Ṁ is (pc-Ė eeqs feqs))) (xs' : Ṁ (X ∘ pull) (und-Ṁ is (pc-Ė eeqs feqs))) →
           ṀHEq (und-Ṁ is (pc-Ė eeqs feqs)) xs xs' →
           ṀHEq is (erase-Ṁ (sc-Ė feqs (diff-Ė-r eeqs feqs)) {X} xs) (erase-Ṁ (to≡-Ṁ is (pc-Ė eeqs feqs)) {X} xs')
    aux' _          []            X _        _          _            = tt
    aux' (_ ∷ eeqs) (refl ∷ feqs) X (x , xs) (x' , xs') (heq , heqs) = heq , aux' eeqs feqs X xs xs' heqs
    aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') → ROrnEq (scROrn P' (diffROrn-r O' P')) (toROrn (pcROrn O' P'))
    aux (ṿ eeqs)          (ṿ feqs)   X xs           xs'           (ṿ heqs)      = ṿ (aux' eeqs feqs X xs xs' heqs)
    aux (ṿ eeqs)          (Δ T P')   X (.t , xs)    (.t , xs')    (σ t heq)    = aux (ṿ eeqs) (P' t) X xs xs' heq
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

module Integration {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

  integrate-Ind : (j : J) → μ E j → Set
  integrate-Ind j y = {k : K} (z : μ F k) → forget O y ≅ forget P z → ∀ jk → π₁ jk ≡ j → π₂ jk ≡ k →
                      Σ[ p ∶ μ ⌊ O ⊗ P ⌋ jk ] forget (diffOrn-l O P) p ≅ y × forget (diffOrn-r O P) p ≅ z

  integrate-aux₀ :
    ∀ {j} (y : μ E j) → ∀ {k} (z : μ F k) → ∀ {i} (eeq : e j ≡ i) → ∀ {i'} (feq : f k ≡ i') → i ≡ i' →
    ∀ {is js ks} (ys : Ṁ (μ E) js) (zs : Ṁ (μ F) ks) (eeqs : Ė e js is) (feqs : Ė f ks is) →
    erase-Ṁ (eeq ∷ eeqs) {μ D} (forget O y , mapFold-Ṁ E (ornAlg O) js ys)
      ≅ erase-Ṁ (feq ∷ feqs) {μ D} (forget P z , mapFold-Ṁ F (ornAlg P) ks zs) →
    forget O y ≅ forget P z × erase-Ṁ eeqs {μ D} (mapFold-Ṁ E (ornAlg O) js ys) ≡ erase-Ṁ feqs {μ D} (mapFold-Ṁ F (ornAlg P) ks zs)
  integrate-aux₀ y z refl refl ieq ys zs eeqs feqs eq = (id ** ≅-to-≡) (cong-split (cong (μ D) ieq) refl eq)

  integrate-aux₁ :
    ∀ {i j k} (y : μ E j) (eeq : e j ≡ i) (feq : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ e eeq , from≡ f feq)) → forget (diffOrn-l O P) p ≅ y →
    ∀ {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṁ (μ ⌊ O ⊗ P ⌋) (und-Ṁ is (pc-Ė eeqs feqs))) →
    {ys : Ṁ (μ E) js} →
    erase-Ṁ (diff-Ė-l eeqs feqs) (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps) ≡ ys →
    erase-Ṁ (_∷_ {j = from≡ e eeq , from≡ f feq} (und-from≡ e eeq) (diff-Ė-l eeqs feqs))
      (forget (diffOrn-l O P) p , mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps) ≡ (y , ys)
  integrate-aux₁ y refl feq p heq eeqs feqs ps eq = cong₂ _,_ (≅-to-≡ heq) eq

  integrate-aux₂ :
    ∀ {i j k} (z : μ F k) (eeq : e j ≡ i) (feq : f k ≡ i) (p : μ ⌊ O ⊗ P ⌋ (from≡ e eeq , from≡ f feq)) → forget (diffOrn-r O P) p ≅ z →
    ∀ {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṁ (μ ⌊ O ⊗ P ⌋) (und-Ṁ is (pc-Ė eeqs feqs))) →
    {zs : Ṁ (μ F) ks} →
    erase-Ṁ (diff-Ė-r eeqs feqs) (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps) ≡ zs →
    erase-Ṁ (_∷_ {j = from≡ e eeq , from≡ f feq} (und-from≡ f feq) (diff-Ė-r eeqs feqs))
      (forget (diffOrn-r O P) p , mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs))  ps) ≡ (z , zs)
  integrate-aux₂ z eeq refl p heq eeqs feqs ps eq = cong₂ _,_ (≅-to-≡ heq) eq

  integrate-aux-Ṁ :
    {is : List I} {js : List J} {ks : List K}
    (eeqs : Ė e js is) (feqs : Ė f ks is) → (ys : Ṁ (μ E) js) → All-Ṁ integrate-Ind js ys → (zs : Ṁ (μ F) ks) →
    erase-Ṁ eeqs {μ D} (mapFold-Ṁ E (ornAlg O) js ys) ≡ erase-Ṁ feqs (mapFold-Ṁ F (ornAlg P) ks zs) →
    Σ[ ps ∶ Ṁ (μ ⌊ O ⊗ P ⌋) (und-Ṁ is (pc-Ė eeqs feqs)) ]
      erase-Ṁ (diff-Ė-l eeqs feqs) (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps) ≡ ys
    × erase-Ṁ (diff-Ė-r eeqs feqs) (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps) ≡ zs
  integrate-aux-Ṁ []           []           _        _          _        _  = tt , refl , refl
  integrate-aux-Ṁ (eeq ∷ eeqs) (feq ∷ feqs) (y , ys) (ih , ihs) (z , zs) eq =
    let (heq , eq') = integrate-aux₀ y z eeq feq refl ys zs eeqs feqs (≡-to-≅ eq)
        (ps , yeqs , zeqs) = integrate-aux-Ṁ eeqs feqs ys ihs zs eq'
        (p  , yeq  , zeq ) = ih z heq _ (und-from≡ e eeq) (und-from≡ f feq)
    in  (p , ps) , integrate-aux₁ y eeq feq p yeq eeqs feqs ps yeqs , integrate-aux₂ z eeq feq p zeq eeqs feqs ps zeqs

  integrate-aux :
    ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') →
    (ys : ⟦ E' ⟧ (μ E)) → All E' integrate-Ind ys → (zs : ⟦ F' ⟧ (μ F)) →
    erase O' {μ D} (mapFold E E' (ornAlg O) ys) ≡ erase P' (mapFold F F' (ornAlg P) zs) →
    Σ[ ps ∶ ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋) ]
      erase (diffROrn-l O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-l O P) {jk}) ps) ≡ ys
    × erase (diffROrn-r O' P') (mapFold ⌊ O ⊗ P ⌋ (toRDesc (pcROrn O' P')) (λ {jk} → ornAlg (diffOrn-r O P) {jk}) ps) ≡ zs
  integrate-aux (ṿ eeqs)    (ṿ feqs)     ys         ihs          zs         eq = integrate-aux-Ṁ eeqs feqs ys ihs zs eq
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
             {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) (ps : Ṁ (μ ⌊ O ⊗ P ⌋) (und-Ṁ is (pc-Ė eeqs feqs))) (heq : _) →
             proj₁ (integrate
                      (forget (diffOrn-l O P) p)
                      (subst (μ F) (und-from≡ f feq) (forget (diffOrn-r O P) p))
                      (proj₁ (integrate-aux₀
                                (forget (diffOrn-l O P) p)
                                (subst (μ F) (und-from≡ f feq) (forget (diffOrn-r O P) p))
                                eeq feq refl
                                (erase-Ṁ (diff-Ė-l eeqs feqs)
                                         (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-l O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps))
                                (erase-Ṁ (diff-Ė-r eeqs feqs)
                                         (mapFold-Ṁ ⌊ O ⊗ P ⌋ (λ {jk} → ornAlg (diffOrn-r O P) {jk}) (und-Ṁ is (pc-Ė eeqs feqs)) ps))
                                eeqs feqs heq))
                      (j , from≡ f feq) refl (und-from≡ f feq)) ≡ p
      aux' j eeq refl p ih heq eeqs feqs ps = ih _ refl refl
      aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f D' F') (ps : ⟦ toRDesc (pcROrn O' P') ⟧ (μ ⌊ O ⊗ P ⌋)) →
            All (toRDesc (pcROrn O' P')) integrate-inv-Ind ps →(eq : _) →
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
      Σ[ q ∶ μ ⌊ O ⊗ P ⌋ (from≡ e (FamMorphismEq.e (SliceMorphism.triangle p'-to-l) i) ,
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

  ⊗-is-Pullback : Pullback Fam l r (object Ind (e ⋈ f , ⌊ O ⊗ P ⌋))
  ⊗-is-Pullback = (span p p-to-l p-to-r , refl) ,
                  λ { (span p' l' r') → Universality.p'-to-p p' l' r' , Universality.uniqueness p' l' r' }

open IsPullback public using (⊗-is-Pullback)
