-- Parallel composition of ornaments.

module Ornament.ParallelComposition where

open import Prelude.InverseImage
open import Description
open import Ornament

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


pc-Ė : {I J K : Set} {e : J → I} {f : K → I} {is : List I} {js : List J} {ks : List K} →
       Ė e js is → Ė f ks is → Ṗ is (InvImage (pull {J} {K} {I} {e} {f}))
pc-Ė             []           []           = tt
pc-Ė {e = e} {f} (eeq ∷ eeqs) (feq ∷ feqs) = ok (from≡ e eeq , from≡ f feq) , pc-Ė eeqs feqs

mutual

  pcROrn : ∀ {I J K} {e : J → I} {f : K → I} {D : RDesc I} {E : RDesc J} {F : RDesc K} → ROrn e D E → ROrn f D F → ROrnDesc (e ⋈ f) pull D
  pcROrn (ṿ eeqs) (ṿ feqs) = ṿ (pc-Ė eeqs feqs)
  pcROrn (ṿ eeqs) (Δ T P)  = Δ[ t ∈ T ] pcROrn (ṿ eeqs) (P t)
  pcROrn (σ S O)  (σ .S P) = σ[ s ∈ S ] pcROrn (O s) (P s)
  pcROrn (σ f O)  (Δ T P)  = Δ[ t ∈ T ] pcROrn (σ f O) (P t)
  pcROrn (σ S O)  (∇ s P)  = ∇ s (pcROrn (O s) P)
  pcROrn (Δ T O)  P        = Δ[ t ∈ T ] pcROrn (O t) P
  pcROrn (∇ s O)  (σ S P)  = ∇ s (pcROrn O (P s))
  pcROrn (∇ s O)  (Δ T P)  = Δ[ t ∈ T ] pcROrn (∇ s O) (P t)
  pcROrn (∇ s O)  (∇ s' P) = Δ (s ≡ s') (pcROrn-double∇ O P)

  pcROrn-double∇ : {I J K S : Set} {e : J → I} {f : K → I} {D : S → RDesc I} {E : RDesc J} {F : RDesc K} {s s' : S} →
                   ROrn e (D s) E → ROrn f (D s') F → s ≡ s' → ROrnDesc (e ⋈ f) pull (σ S D)
  pcROrn-double∇ {s = s} O P refl = ∇ s (pcROrn O P)

_⊗_ : ∀ {I J K} {e : J → I} {f : K → I} {D E F} → Orn e D E → Orn f D F → OrnDesc (e ⋈ f) pull D
_⊗_ {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → pcROrn (O j) (P k) }


-- left difference ornament

diff-Ė-l : ∀ {I J K} {e : J → I} {f : K → I} {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) → Ė π₁ (und-Ṗ is (pc-Ė eeqs feqs)) js
diff-Ė-l         []           _            = []
diff-Ė-l {e = e} (eeq ∷ eeqs) (feq ∷ feqs) = und-from≡ e eeq ∷ diff-Ė-l eeqs feqs

mutual

  diffROrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
               (O : ROrn e D E) (P : ROrn f D F) → ROrn π₁ E (toRDesc (pcROrn O P))
  diffROrn-l (ṿ eeqs) (ṿ feqs) = ṿ (diff-Ė-l eeqs feqs)
  diffROrn-l (ṿ eeqs) (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (ṿ eeqs) (P t)
  diffROrn-l (σ S O)  (σ .S P) = σ[ s ∈ S ] diffROrn-l (O s) (P s)
  diffROrn-l (σ S O)  (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (σ S O) (P t)
  diffROrn-l (σ S O)  (∇ s P)  = ∇ s (diffROrn-l (O s) P)
  diffROrn-l (Δ T O)  P        = σ[ t ∈ T ] diffROrn-l (O t) P
  diffROrn-l (∇ s O)  (σ S P)  = diffROrn-l O (P s)
  diffROrn-l (∇ s O)  (Δ T P)  = Δ[ t ∈ T ] diffROrn-l (∇ s O) (P t)
  diffROrn-l (∇ s O)  (∇ s' P) = Δ (s ≡ s') (diffROrn-l-double∇ O P)

  diffROrn-l-double∇ : ∀ {I J K} {e : J → I} {f : K → I} {S} {D E F} {s s' : S} →
                       (O : ROrn e (D s) E) (P : ROrn f (D s') F) (eq : s ≡ s') →
                       ROrn π₁ E (toRDesc (pcROrn-double∇ {D = D} O P eq))
  diffROrn-l-double∇ O P refl = diffROrn-l O P

diffOrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
            (O : Orn e D E) (P : Orn f D F) → Orn π₁ E ⌊ O ⊗ P ⌋
diffOrn-l {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → diffROrn-l (O j) (P k) }


-- right difference ornament

diff-Ė-r : ∀ {I J K} {e : J → I} {f : K → I} {is js ks} (eeqs : Ė e js is) (feqs : Ė f ks is) → Ė π₂ (und-Ṗ is (pc-Ė eeqs feqs)) ks
diff-Ė-r         _            []           = []
diff-Ė-r {f = f} (eeq ∷ eeqs) (feq ∷ feqs) = und-from≡ f feq ∷ diff-Ė-r eeqs feqs

mutual

  diffROrn-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F} →
               (O : ROrn e D E) (P : ROrn f D F) → ROrn π₂ F (toRDesc (pcROrn O P))
  diffROrn-r (ṿ eeqs) (ṿ feqs) = ṿ (diff-Ė-r eeqs feqs)
  diffROrn-r (ṿ idx)  (Δ T P)  = σ[ t ∈ T ] diffROrn-r (ṿ idx) (P t)
  diffROrn-r (σ S O)  (σ .S P) = σ[ s ∈ S ] diffROrn-r (O s) (P s)
  diffROrn-r (σ S O)  (Δ T P)  = σ[ t ∈ T ] diffROrn-r (σ S O) (P t)
  diffROrn-r (σ S O)  (∇ s P)  = diffROrn-r (O s) P
  diffROrn-r (Δ T O)  P        = Δ[ t ∈ T ] diffROrn-r (O t) P
  diffROrn-r (∇ s O)  (σ S P)  = ∇ s (diffROrn-r O (P s))
  diffROrn-r (∇ s O)  (Δ T P)  = σ[ t ∈ T ] diffROrn-r (∇ s O) (P t)
  diffROrn-r (∇ s O) (∇ s' P)  = Δ (s ≡ s') (diffROrn-r-double∇ O P)

  diffROrn-r-double∇ : ∀ {I J K} {e : J → I} {f : K → I} {S} {D E F} {s s' : S} →
                       (O : ROrn e (D s) E) (P : ROrn f (D s') F) (eq : s ≡ s') →
                       ROrn π₂ F (toRDesc (pcROrn-double∇ {D = D} O P eq))
  diffROrn-r-double∇ O P refl = diffROrn-r O P

diffOrn-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
            (O : Orn e D E) (P : Orn f D F) → Orn π₂ F ⌊ O ⊗ P ⌋
diffOrn-r {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → diffROrn-r (O j) (P k) }
