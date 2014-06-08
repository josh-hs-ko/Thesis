-- Sequential composition of ornaments.

module Ornament.SequentialComposition where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.Equivalence

open import Function using (_∘_; const; id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡; module ≅-Reasoning) renaming (refl to hrefl)


scROrn : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → ROrn e D E → ROrn f E F → ROrn (e ∘ f) D F
scROrn (ṿ eeqs) (ṿ feqs) = ṿ (Ė-trans eeqs feqs)
scROrn (ṿ eeqs) (Δ T P)  = Δ[ t ∈ T ] scROrn (ṿ eeqs) (P t)
scROrn (σ S O)  (σ .S P) = σ S λ s → scROrn (O s) (P s)
scROrn (σ S O)  (Δ T P)  = Δ[ t ∈ T ] scROrn (σ S O) (P t)
scROrn (σ S O)  (∇ s P)  = ∇ s (scROrn (O s) P)
scROrn (Δ T O)  (σ .T P) = Δ[ t ∈ T ] scROrn (O t) (P t)
scROrn (Δ T O)  (Δ T' P) = Δ[ t ∈ T' ] scROrn (Δ T O) (P t)
scROrn (Δ T O)  (∇ t P)  = scROrn (O t) P
scROrn (∇ s O)  P        = ∇ s (scROrn O P)

_⊙_ : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → Orn e D E → Orn f E F → Orn (e ∘ f) D F
_⊙_ {f = f} (wrap O) (wrap O') = wrap λ { {._} (ok k) → scROrn (O (ok (f k))) (O' (ok k)) }

shift-Δ : ∀ {I J K T} {e : J → I} {f : K → J} {D E F} → (O : ROrn e D E) (P : (t : T) → ROrn f E (F t)) →
          {X : List I → Set} {Y : List K → Set} (g : Erasure (e ∘ f) Y X) (ys : Ḣ (σ T F) Y) →
          erase' (scROrn O (Δ T P)) g ys ≡ erase' (Δ T λ t → scROrn O (P t)) g ys
shift-Δ (ṿ eqs)  P g (t , ys) = refl
shift-Δ (σ S O)  P g (t , ys) = refl
shift-Δ (Δ T O)  P g (t , ys) = refl
shift-Δ (∇ s O)  P g (t , ys) = cong (_,_ s) (shift-Δ O P g (t , ys))

erase-Ṡ-scROrn :
  ∀ {I J K} {e : J → I} {f : K → J} {D E F} (O : ROrn e D E) (P : ROrn f E F) → erase-Ṡ (scROrn O P) ≐ erase-Ṡ O ∘ erase-Ṡ P
erase-Ṡ-scROrn (ṿ eeqs)          (ṿ feqs)          _        = refl
erase-Ṡ-scROrn (ṿ eeqs)          (Δ T P)           (t , hs) = erase-Ṡ-scROrn (ṿ eeqs) (P t) hs
erase-Ṡ-scROrn (σ S O)           (σ .S P)          (s , hs) = cong (_,_ s) (erase-Ṡ-scROrn (O s) (P s) hs)
erase-Ṡ-scROrn (σ S O)           (Δ T P)           (t , hs) = erase-Ṡ-scROrn (σ S O) (P t) hs
erase-Ṡ-scROrn (σ S O)           (∇ s P)           hs       = cong (_,_ s) (erase-Ṡ-scROrn (O s) P hs)
erase-Ṡ-scROrn (Δ T O)           (σ .T P)          (t , hs) = erase-Ṡ-scROrn (O t) (P t) hs
erase-Ṡ-scROrn (Δ T O)           (Δ U P)           (u , hs) = erase-Ṡ-scROrn (Δ T O) (P u) hs
erase-Ṡ-scROrn (Δ T O)           (∇ t P)           hs       = erase-Ṡ-scROrn (O t) P hs
erase-Ṡ-scROrn (∇ s O)           P                 hs       = cong (_,_ s) (erase-Ṡ-scROrn O P hs)

forget-after-forget :
  ∀ {I J K} {e : J → I} {f : K → J} {D E F} (O : Orn e D E) (P : Orn f E F) →
  ∀ {k} (x : μ F k) → forget (O ⊙ P) x ≡ forget O (forget P x)
forget-after-forget {e = e} {f} {D} {E} {F} O P =
  induction F (λ _ x → forget (O ⊙ P) x ≡ forget O (forget P x))
              (λ i fs all → cong con (aux (Orn.comp O (ok (f i))) (Orn.comp P (ok i)) fs all))
  where
    aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f E' F') →
          (fs : ⟦ F' ⟧ (μ F)) → All F' (λ _ x → forget (O ⊙ P) x ≡ forget O (forget P x)) fs →
          erase (scROrn O' P') {μ D} (mapFold F F' (ornAlg (O ⊙ P)) fs)
            ≡ erase O' (mapFold E E' (ornAlg O) (erase P' (mapFold F F' (ornAlg P) fs)))
    aux (ṿ [])            (ṿ [])            _        _          = refl
    aux (ṿ (refl ∷ eeqs)) (ṿ (refl ∷ feqs)) (f , fs) (ih , ihs) = cong₂ _,_ ih (aux (ṿ eeqs) (ṿ feqs) fs ihs)
    aux (ṿ eeqs)          (Δ T P')          (t , fs) ihs        = aux (ṿ eeqs) (P' t) fs ihs
    aux (σ S O')          (σ .S P')         (s , fs) ihs        = cong (_,_ s) (aux (O' s) (P' s) fs ihs)
    aux (σ S O')          (Δ T P')          (t , fs) ihs        = aux (σ S O') (P' t) fs ihs
    aux (σ S O')          (∇ s P')          fs       ihs        = cong (_,_ s) (aux (O' s) P' fs ihs)
    aux (Δ T O')          (σ .T P')         (t , fs) ihs        = aux (O' t) (P' t) fs ihs
    aux (Δ T O')          (Δ U P')          (u , fs) ihs        = aux (Δ T O') (P' u) fs ihs
    aux (Δ T O')          (∇ t P')          fs       ihs        = aux (O' t) P' fs ihs
    aux (∇ s O')          P'                fs       ihs        = cong (_,_ s) (aux O' P' fs ihs)

idROrn-id-l : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ROrnEq (scROrn (idROrn D) O) O
idROrn-id-l {D = D} O hs =
  ≡-to-≅ (begin
            erase-Ṡ (scROrn (idROrn D) O) hs
              ≡⟨ erase-Ṡ-scROrn (idROrn D) O hs ⟩
            erase-Ṡ (idROrn D) (erase-Ṡ O hs)
              ≡⟨ erase'-idROrn D (const !) (erase-Ṡ O hs) ⟩
            Ḣ-map D id (erase-Ṡ O hs)
              ≡⟨ Ḣ-map-preserves-id D (erase-Ṡ O hs) ⟩
            erase-Ṡ O hs
          ∎)
  where open ≡-Reasoning

⊙-id-l : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → OrnEq (idOrn D ⊙ O) O
⊙-id-l (wrap O) = frefl , λ j → idROrn-id-l (O (ok j))

idROrn-id-r : ∀ {I J} {e : J → I} {D E} (O : ROrn e D E) → ROrnEq (scROrn O (idROrn E)) O
idROrn-id-r {E = E} O hs =
  ≡-to-≅ (begin
            erase-Ṡ (scROrn O (idROrn E)) hs
              ≡⟨ erase-Ṡ-scROrn O (idROrn E) hs ⟩
            erase-Ṡ O (erase-Ṡ (idROrn E) hs)
              ≡⟨ cong (erase-Ṡ O) (erase'-idROrn E (const !) hs) ⟩
            erase-Ṡ O (Ḣ-map E id hs)
              ≡⟨ cong (erase-Ṡ O) (Ḣ-map-preserves-id E hs) ⟩
            erase-Ṡ O hs
          ∎)
  where open ≡-Reasoning

⊙-id-r : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → OrnEq (O ⊙ idOrn E) O
⊙-id-r (wrap O) = frefl , λ j → idROrn-id-r (O (ok j))

scROrn-assoc :
  ∀ {I J K L} {e : J → I} {f : K → J} {g : L → K} {D E F G}
  (O : ROrn e D E) (P : ROrn f E F) (Q : ROrn g F G) → ROrnEq (scROrn (scROrn O P) Q) (scROrn O (scROrn P Q))
scROrn-assoc {e = e} {f} {g} {D = D} {G = G} O P Q hs =
  ≡-to-≅ (begin
            erase-Ṡ (scROrn (scROrn O P) Q) hs
              ≡⟨ erase-Ṡ-scROrn (scROrn O P) Q hs ⟩
            erase-Ṡ (scROrn O P) (erase-Ṡ Q hs)
              ≡⟨ erase-Ṡ-scROrn O P (erase-Ṡ Q hs) ⟩
            erase-Ṡ O (erase-Ṡ P (erase-Ṡ Q hs))
              ≡⟨ sym (cong (erase-Ṡ O) (erase-Ṡ-scROrn P Q hs)) ⟩
            erase-Ṡ O (erase-Ṡ (scROrn P Q) hs)
              ≡⟨ sym (erase-Ṡ-scROrn O (scROrn P Q) hs) ⟩
            erase-Ṡ (scROrn O (scROrn P Q)) hs
          ∎)
  where open ≡-Reasoning

⊙-assoc : ∀ {I J K L} {e : J → I} {f : K → J} {g : L → K} {D E F G}
          (O : Orn e D E) (P : Orn f E F) (Q : Orn g F G) → OrnEq ((O ⊙ P) ⊙ Q) (O ⊙ (P ⊙ Q))
⊙-assoc {e = e} {f} {g} {D = D} {G = G} O P Q =
  frefl , (λ l → scROrn-assoc (Orn.comp O (ok (f (g l)))) (Orn.comp P (ok (g l))) (Orn.comp Q (ok l)))

scROrn-cong-l : ∀ {I J K} {e e' : J → I} {f : I → K} {D D' E F F'}
                (Q : ROrn f F D) (Q' : ROrn f F' D') (O : ROrn e D E) (P : ROrn e' D' E) →
                D ≡ D' → F ≡ F' → Q ≅ Q' → ROrnEq O P → ROrnEq (scROrn Q O) (scROrn Q' P)
scROrn-cong-l Q .Q O P refl refl hrefl roeq hs =
  ≡-to-≅ (begin
            erase-Ṡ (scROrn Q O) hs
              ≡⟨ erase-Ṡ-scROrn Q O hs ⟩
            erase-Ṡ Q (erase-Ṡ O hs)
              ≡⟨ cong (erase-Ṡ Q) (≅-to-≡ (roeq hs)) ⟩
            erase-Ṡ Q (erase-Ṡ P hs)
              ≡⟨ sym (erase-Ṡ-scROrn Q P hs) ⟩
            erase-Ṡ (scROrn Q P) hs
          ∎)
  where open ≡-Reasoning

⊙-cong-l : ∀ {I J K} {e e' : J → I} {f : I → K} {D E F}
           (Q : Orn f F D) (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq (Q ⊙ O) (Q ⊙ P)
⊙-cong-l {e = e} {e'} {f} {D} {E} {F} Q O P (eeq , oeq) =
  fcong-l f eeq ,
  λ j → scROrn-cong-l (Orn.comp Q (ok (e j))) (Orn.comp Q (ok (e' j))) (Orn.comp O (ok j)) (Orn.comp P (ok j))
                      (cong (Desc.comp D) (eeq j)) (cong (Desc.comp F ∘ f) (eeq j))
                      (subst (λ i → Orn.comp Q (ok (e j)) ≅ Orn.comp Q (ok i)) (eeq j) hrefl) (oeq j)

⊙-cong-r : ∀ {I J K} {e e' : J → I} {f : K → J} {D E F}
           (Q : Orn f E F) (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq (O ⊙ Q) (P ⊙ Q)
⊙-cong-r {e = e} {e'} {f} {D} {E} {F} Q O P (eeq , oeq) =
  fcong-r f eeq ,
  λ k hs → begin
             erase-Ṡ (scROrn (Orn.comp O (ok (f k))) (Orn.comp Q (ok k))) hs
               ≅⟨ ≡-to-≅ (erase-Ṡ-scROrn (Orn.comp O (ok (f k))) (Orn.comp Q (ok k)) hs) ⟩
             erase-Ṡ (Orn.comp O (ok (f k))) (erase-Ṡ (Orn.comp Q (ok k)) hs)
               ≅⟨ oeq (f k) (erase-Ṡ (Orn.comp Q (ok k)) hs) ⟩
             erase-Ṡ (Orn.comp P (ok (f k))) (erase-Ṡ (Orn.comp Q (ok k)) hs)
               ≅⟨ ≡-to-≅ (sym (erase-Ṡ-scROrn (Orn.comp P (ok (f k))) (Orn.comp Q (ok k)) hs)) ⟩
             erase-Ṡ (scROrn (Orn.comp P (ok (f k))) (Orn.comp Q (ok k))) hs
           ∎
  where open ≅-Reasoning
