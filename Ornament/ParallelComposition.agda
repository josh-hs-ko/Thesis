-- Parallel composition of ornaments.

module Ornament.ParallelComposition where

open import Prelude.InverseImage
open import Description
open import Ornament

open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


mutual

  pcROrn : ∀ {I J K} {e : J → I} {f : K → I} {D E F} → ROrn e D E → ROrn f D F → ROrnDesc (e ⋈ f) pull D
  pcROrn ∎        ∎        = ∎
  pcROrn ∎        (Δ T P)  = Δ[ t ∶ T ] pcROrn ∎ (P t)
  pcROrn (ṿ idx)  (ṿ idx') = ṿ (ok (from≡ idx , from≡ idx'))
  pcROrn (ṿ idx)  (Δ T P)  = Δ[ t ∶ T ] pcROrn (ṿ idx) (P t)
  pcROrn (σ S O)  (σ .S P) = σ[ s ∶ S ] pcROrn (O s) (P s)
  pcROrn (σ f O)  (Δ T P)  = Δ[ t ∶ T ] pcROrn (σ f O) (P t)
  pcROrn (σ S O)  (∇ s P)  = ∇ s (pcROrn (O s) P)
  pcROrn (Δ T O)  P        = Δ[ t ∶ T ] pcROrn (O t) P
  pcROrn (∇ s O)  (σ S P)  = ∇ s (pcROrn O (P s))
  pcROrn (∇ s O)  (Δ T P)  = Δ[ t ∶ T ] pcROrn (∇ s O) (P t)
  pcROrn (∇ s O)  (∇ s' P) = Δ (s ≡ s') (pcROrn-double∇ O P)
  pcROrn (O * O') (Δ T P)  = Δ[ t ∶ T ] pcROrn (O * O') (P t)
  pcROrn (O * O') (P * P') = pcROrn O P * pcROrn O' P'

  pcROrn-double∇ : ∀ {I J K S} {e : J → I} {f : K → I} {D E F} {s s' : S} →
                   ROrn e (D s) E → ROrn f (D s') F → s ≡ s' → ROrnDesc (e ⋈ f) pull (σ S D)
  pcROrn-double∇ {s = s} O P refl = ∇ s (pcROrn O P)

_⊗_ : ∀ {I J K} {e : J → I} {f : K → I} {D E F} → Orn e D E → Orn f D F → OrnDesc (e ⋈ f) pull D
_⊗_ {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → pcROrn (O j) (P k) }


-- left difference ornament

mutual

  diffROrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
               (O : ROrn e D E) (P : ROrn f D F) → ROrn π₁ E (toRDesc (pcROrn O P))
  diffROrn-l ∎        ∎        = ∎
  diffROrn-l ∎        (Δ T P)  = Δ T λ t → diffROrn-l ∎ (P t)
  diffROrn-l (ṿ refl) (ṿ idx') = ṿ refl
  diffROrn-l (ṿ idx)  (Δ T P)  = Δ T λ t → diffROrn-l (ṿ idx) (P t)
  diffROrn-l (σ S O)  (σ .S P) = σ S λ s → diffROrn-l (O s) (P s)
  diffROrn-l (σ S O)  (Δ T P)  = Δ T λ t → diffROrn-l (σ S O) (P t)
  diffROrn-l (σ S O)  (∇ s P)  = ∇ s (diffROrn-l (O s) P)
  diffROrn-l (Δ T O)  P        = σ T λ t → diffROrn-l (O t) P
  diffROrn-l (∇ s O)  (σ S P)  = diffROrn-l O (P s)
  diffROrn-l (∇ s O)  (Δ T P)  = Δ T λ t → diffROrn-l (∇ s O) (P t)
  diffROrn-l (∇ s O)  (∇ s' P) = Δ (s ≡ s') (diffROrn-l-double∇ O P)
  diffROrn-l (O * O') (Δ T P)  = Δ T λ t → diffROrn-l (O * O') (P t)
  diffROrn-l (O * O') (P * P') = diffROrn-l O P * diffROrn-l O' P'

  diffROrn-l-double∇ : ∀ {I J K} {e : J → I} {f : K → I} {S} {D E F} {s s' : S} →
                       (O : ROrn e (D s) E) (P : ROrn f (D s') F) (eq : s ≡ s') →
                       ROrn π₁ E (toRDesc (pcROrn-double∇ {D = D} O P eq))
  diffROrn-l-double∇ O P refl = diffROrn-l O P

diffOrn-l : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
            (O : Orn e D E) (P : Orn f D F) → Orn π₁ E ⌊ O ⊗ P ⌋
diffOrn-l {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → diffROrn-l (O j) (P k) }


-- right difference ornament

mutual

  diffROrn-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F} →
               (O : ROrn e D E) (P : ROrn f D F) → ROrn π₂ F (toRDesc (pcROrn O P))
  diffROrn-r ∎        ∎        = ∎
  diffROrn-r ∎        (Δ T P)  = σ T λ t → diffROrn-r ∎ (P t)
  diffROrn-r (ṿ idx)  (ṿ refl) = ṿ refl
  diffROrn-r (ṿ idx)  (Δ T P)  = σ T λ t → diffROrn-r (ṿ idx) (P t)
  diffROrn-r (σ S O)  (σ .S P) = σ S λ s → diffROrn-r (O s) (P s)
  diffROrn-r (σ S O)  (Δ T P)  = σ T λ t → diffROrn-r (σ S O) (P t)
  diffROrn-r (σ S O)  (∇ s P)  = diffROrn-r (O s) P
  diffROrn-r (Δ T O)  P        = Δ T λ t → diffROrn-r (O t) P
  diffROrn-r (∇ s O)  (σ S P)  = ∇ s (diffROrn-r O (P s))
  diffROrn-r (∇ s O)  (Δ T P)  = σ T λ t → diffROrn-r (∇ s O) (P t)
  diffROrn-r (∇ s O) (∇ s' P)  = Δ (s ≡ s') (diffROrn-r-double∇ O P)
  diffROrn-r (O * O') (Δ T P)  = σ T λ t → diffROrn-r (O * O') (P t)
  diffROrn-r (O * O') (P * P') = diffROrn-r O P * diffROrn-r O' P'

  diffROrn-r-double∇ : ∀ {I J K} {e : J → I} {f : K → I} {S} {D E F} {s s' : S} →
                       (O : ROrn e (D s) E) (P : ROrn f (D s') F) (eq : s ≡ s') →
                       ROrn π₂ F (toRDesc (pcROrn-double∇ {D = D} O P eq))
  diffROrn-r-double∇ O P refl = diffROrn-r O P

diffOrn-r : ∀ {I J K} {e : J → I} {f : K → I} {D E F}
            (O : Orn e D E) (P : Orn f D F) → Orn π₂ F ⌊ O ⊗ P ⌋
diffOrn-r {e = e} {f} {D} {E} {F} (wrap O) (wrap P) = wrap λ { {._} (ok (j , k)) → diffROrn-r (O j) (P k) }
