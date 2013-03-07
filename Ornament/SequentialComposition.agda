-- Sequential composition of ornaments.

module Thesis.Ornament.SequentialComposition where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Description.HorizontalEquivalence
open import Thesis.Ornament
open import Thesis.Ornament.Equivalence

open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_)


sc-Ė : ∀ {I J K} {e : J → I} {f : K → J} {is js ks} → Ė e js is → Ė f ks js → Ė (e ∘ f) ks is
sc-Ė         []           []           = []
sc-Ė {e = e} (eeq ∷ eeqs) (feq ∷ feqs) = trans (cong e feq) eeq ∷ sc-Ė eeqs feqs

scROrn : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → ROrn e D E → ROrn f E F → ROrn (e ∘ f) D F
scROrn (ṿ eeqs) (ṿ feqs) = ṿ (sc-Ė eeqs feqs)
scROrn (ṿ eeqs) (Δ T P)  = Δ[ t ∶ T ] scROrn (ṿ eeqs) (P t)
scROrn (σ S O)  (σ .S P) = σ S λ s → scROrn (O s) (P s)
scROrn (σ S O)  (Δ T P)  = Δ[ t ∶ T ] scROrn (σ S O) (P t)
scROrn (σ S O)  (∇ s P)  = ∇ s (scROrn (O s) P)
scROrn (Δ T O)  (σ .T P) = Δ[ t ∶ T ] scROrn (O t) (P t)
scROrn (Δ T O)  (Δ T' P) = Δ[ t ∶ T' ] scROrn (Δ T O) (P t)
scROrn (Δ T O)  (∇ t P)  = scROrn (O t) P
scROrn (∇ s O)  P        = ∇ s (scROrn O P)

_⊙_ : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → Orn e D E → Orn f E F → Orn (e ∘ f) D F
_⊙_ {f = f} (wrap O) (wrap O') = wrap λ { {._} (ok k) → scROrn (O (ok (f k))) (O' (ok k)) }

shiftΔ : ∀ {I J K T} {e : J → I} {f : K → J} {D E F} → (O : ROrn e D E) (P : (t : T) → ROrn f E (F t)) →
         {X : I → Set} (xs : ⟦ σ T F ⟧ (X ∘ e ∘ f)) → erase (Δ T λ t → scROrn O (P t)) {X} xs ≡ erase (scROrn O (Δ T P)) xs
shiftΔ (ṿ eqs)  P (t , xs) = refl
shiftΔ (σ S O)  P (t , xs) = refl
shiftΔ (Δ T O)  P (t , xs) = refl
shiftΔ (∇ s O)  P (t , xs) = cong (_,_ s) (shiftΔ O P (t , xs))

erase-after-erase : ∀ {I J K} {e : J → I} {f : K → J} {D E F} (O : ROrn e D E) (P : ROrn f E F) →
                    ∀ {X} (xs : ⟦ F ⟧ (X ∘ e ∘ f)) → erase (scROrn O P) {X} xs ≡ erase O {X} (erase P {X ∘ e} xs)
erase-after-erase (ṿ [])            (ṿ feqs)          xs       = refl
erase-after-erase (ṿ (refl ∷ eeqs)) (ṿ (refl ∷ feqs)) (x , xs) = cong₂ _,_ refl (erase-after-erase (ṿ eeqs) (ṿ feqs) xs)
erase-after-erase (ṿ eeqs)          (Δ T P)           (t , xs) = erase-after-erase (ṿ eeqs) (P t) xs
erase-after-erase (σ S O)           (σ .S P)          (s , xs) = cong (_,_ s) (erase-after-erase (O s) (P s) xs)
erase-after-erase (σ S O)           (Δ T P)           (t , xs) = erase-after-erase (σ S O) (P t) xs
erase-after-erase (σ S O)           (∇ s P)           xs       = cong (_,_ s) (erase-after-erase (O s) P xs)
erase-after-erase (Δ T O)           (σ .T P)          (t , xs) = erase-after-erase (O t) (P t) xs
erase-after-erase (Δ T O)           (Δ U P)           (u , xs) = erase-after-erase (Δ T O) (P u) xs
erase-after-erase (Δ T O)           (∇ t P)           xs       = erase-after-erase (O t) P xs
erase-after-erase (∇ s O)           P                 xs       = cong (_,_ s) (erase-after-erase O P xs)

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

idROrn-id-l : ∀ {I J} {e : J → I} {D E} (O : ROrn e D E) → ROrnEq (scROrn (idROrn D) O) O
idROrn-id-l {D = D} {E} O X xs xs' heq with HoriEq-to-≡ E xs xs' heq
idROrn-id-l {D = D} {E} O X xs .xs heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (scROrn (idROrn D) O) xs
         ≡⟨ erase-after-erase (idROrn D) O xs ⟩
       erase (idROrn D) (erase O xs)
         ≡⟨ erase-idROrn D ⟩
       erase O xs
     □)
  where open ≡-Reasoning renaming (_∎ to _□)

⊙-id-l : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → OrnEq (idOrn D ⊙ O) O
⊙-id-l (wrap O) = frefl , λ j → idROrn-id-l (O (ok j))

idROrn-id-r : ∀ {I J} {e : J → I} {D E} (O : ROrn e D E) → ROrnEq (scROrn O (idROrn E)) O
idROrn-id-r {D = D} {E} O X xs xs' heq with HoriEq-to-≡ E xs xs' heq
idROrn-id-r {D = D} {E} O X xs .xs heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (scROrn O (idROrn E)) xs
         ≡⟨ erase-after-erase O (idROrn E) xs ⟩
       erase O (erase (idROrn E) xs)
         ≡⟨ cong (erase O) (erase-idROrn E) ⟩
       erase O xs
     □)
  where open ≡-Reasoning renaming (_∎ to _□)

⊙-id-r : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → OrnEq (O ⊙ idOrn E) O
⊙-id-r (wrap O) = frefl , λ j → idROrn-id-r (O (ok j))

scROrn-assoc :
  ∀ {I J K L} {e : J → I} {f : K → J} {g : L → K} {D E F G}
  (O : ROrn e D E) (P : ROrn f E F) (Q : ROrn g F G) → ROrnEq (scROrn (scROrn O P) Q) (scROrn O (scROrn P Q))
scROrn-assoc {e = e} {f} {g} {D = D} {G = G} O P Q X xs xs' heq =
  HoriEq-from-≡ D
    (begin
       erase (scROrn (scROrn O P) Q) xs
         ≡⟨ erase-after-erase (scROrn O P) Q xs ⟩
       erase (scROrn O P) (erase Q xs)
         ≡⟨ erase-after-erase O P (erase Q xs) ⟩
       erase O (erase P (erase Q xs))
         ≡⟨ cong (erase O) (sym (erase-after-erase P Q xs)) ⟩
       erase O (erase (scROrn P Q) xs)
         ≡⟨ sym (erase-after-erase O (scROrn P Q) xs) ⟩
       erase (scROrn O (scROrn P Q)) xs
         ≡⟨ cong (erase (scROrn O (scROrn P Q))) (HoriEq-to-≡ G xs xs' heq) ⟩
       erase (scROrn O (scROrn P Q)) xs'
     □)
  where open ≡-Reasoning renaming (_∎ to _□)

⊙-assoc : ∀ {I J K L} {e : J → I} {f : K → J} {g : L → K} {D E F G}
          (O : Orn e D E) (P : Orn f E F) (Q : Orn g F G) → OrnEq ((O ⊙ P) ⊙ Q) (O ⊙ (P ⊙ Q))
⊙-assoc {e = e} {f} {g} {D = D} {G = G} O P Q =
  frefl , (λ l → scROrn-assoc (Orn.comp O (ok (f (g l)))) (Orn.comp P (ok (g l))) (Orn.comp Q (ok l)))

scROrn-cong-l : ∀ {I J K} {e e' : J → I} {f : I → K} {D D' E F F'} → D ≡ D' → F ≡ F' →
                (Q : ROrn f F D) (Q' : ROrn f F' D') (O : ROrn e D E) (P : ROrn e' D' E) →
                ROrnEq Q Q' → ROrnEq O P → ROrnEq (scROrn Q O) (scROrn Q' P)
scROrn-cong-l {f = f} {D = D} {F = F} refl refl Q Q' O P qeq oeq X xs xs' heq =
  HoriEq-from-≡ F
    (begin
       erase (scROrn Q O) xs
         ≡⟨ erase-after-erase Q O xs ⟩
       erase Q (erase O xs)
         ≡⟨ cong (erase Q) (HoriEq-to-≡ D (erase O xs) (erase P xs') (oeq (X ∘ f) xs xs' heq)) ⟩
       erase Q (erase P xs')
         ≡⟨ HoriEq-to-≡ F (erase Q (erase P xs')) (erase Q' (erase P xs')) (qeq X (erase P xs') (erase P xs') (HoriEq-from-≡ D refl)) ⟩
       erase Q' (erase P xs')
         ≡⟨ sym (erase-after-erase Q' P xs') ⟩
       erase (scROrn Q' P) xs'
     □)
  where open ≡-Reasoning renaming (_∎ to _□)

⊙-cong-l : ∀ {I J K} {e e' : J → I} {f : I → K} {D E F}
           (Q : Orn f F D) (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq (Q ⊙ O) (Q ⊙ P)
⊙-cong-l {e = e} {e'} {f} {D} {E} {F} Q O P (eeq , oeq) =
  fcong-l f eeq ,
  λ j → scROrn-cong-l (cong (Desc.comp D) (eeq j)) (cong (Desc.comp F ∘ f) (eeq j))
                      (Orn.comp Q (ok (e j))) (Orn.comp Q (ok (e' j))) (Orn.comp O (ok j)) (Orn.comp P (ok j))
                      (subst (λ i → ROrnEq (Orn.comp Q (ok (e j))) (Orn.comp Q (ok i))) (eeq j) (ROrnEq-refl (Orn.comp Q (ok (e j))))) (oeq j)

scROrn-cong-r : ∀ {I J K} {e e' : J → I} {f : K → J} {D D' E F} → D ≡ D' →
                (Q : ROrn f E F) (O : ROrn e D E) (P : ROrn e' D' E) → ROrnEq O P → ROrnEq (scROrn O Q) (scROrn P Q)
scROrn-cong-r {I} {J} {K} {e} {e'} {f} {D} {._} {E} {F} refl Q O P oeq X xs xs' heq =
  HoriEq-from-≡ D
    (begin
       erase (scROrn O Q) xs
         ≡⟨ erase-after-erase O Q xs ⟩
       erase O (erase Q xs)
         ≡⟨ HoriEq-to-≡ D (erase O (erase Q xs)) (erase P (erase Q xs')) (oeq X (erase Q xs) (erase Q xs') (aux Q xs xs' heq)) ⟩
       erase P (erase Q xs')
         ≡⟨ sym (erase-after-erase P Q xs') ⟩
       erase (scROrn P Q) xs'
     □)
  where
    open ≡-Reasoning renaming (_∎ to _□)
    aux' : {js : List J} {ks : List K} →
           (eqs : Ė f ks js) (xs : Ṁ (X ∘ e ∘ f) ks) (xs' : Ṁ (X ∘ e' ∘ f) ks) →
           ṀHEq ks xs xs' → ṀHEq js (erase-Ṁ eqs {X ∘ e} xs) (erase-Ṁ eqs {X ∘ e'} xs')
    aux' []           _        _          _            = tt
    aux' (refl ∷ eqs) (x , xs) (x' , xs') (heq , heqs) = heq , aux' eqs xs xs' heqs
    aux : ∀ {E F} (Q : ROrn f E F) (xs : ⟦ F ⟧ (X ∘ e ∘ f)) (xs' : ⟦ F ⟧ (X ∘ e' ∘ f)) →
          HoriEq F xs F xs' → HoriEq E (erase Q {X ∘ e} xs) E (erase Q {X ∘ e'} xs')
    aux (ṿ eqs) xs        xs'         (ṿ heq)      = ṿ (aux' eqs xs xs' heq)
    aux (σ S Q) (.s , xs) (.s , xs')  (σ s heq)    = σ s (aux (Q s) xs xs' heq)
    aux (Δ T Q) (.t , xs) (.t , xs')  (σ t heq)    = aux (Q t) xs xs' heq
    aux (∇ s Q) xs        xs'         heq          = σ s (aux Q xs xs' heq)

⊙-cong-r : ∀ {I J K} {e e' : J → I} {f : K → J} {D E F}
           (Q : Orn f E F) (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq (O ⊙ Q) (P ⊙ Q)
⊙-cong-r {e = e} {e'} {f} {D} {E} {F} Q O P (eeq , oeq) =
  fcong-r f eeq ,
  λ k → scROrn-cong-r (cong (Desc.comp D) (eeq (f k))) (Orn.comp Q (ok k)) (Orn.comp O (ok (f k))) (Orn.comp P (ok (f k))) (oeq (f k))
