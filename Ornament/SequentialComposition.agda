-- Sequential composition of ornaments.

module Ornament.SequentialComposition where

open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Description.HorizontalEquivalence
open import Ornament
open import Ornament.Equivalence

open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_)


scROrn : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → ROrn e D E → ROrn f E F → ROrn (e ∘ f) D F
scROrn         ∎        ∎        = ∎
scROrn {e = e} ∎        (Δ T P)  = Δ[ t ∶ T ] scROrn {e = e} ∎ (P t)
scROrn         (ṿ refl) (ṿ refl) = ṿ refl
scROrn {e = e} (ṿ idx)  (Δ T P)  = Δ[ t ∶ T ] scROrn {e = e} (ṿ idx) (P t)
scROrn         (σ S O)  (σ .S P) = σ S λ s → scROrn (O s) (P s)
scROrn         (σ S O)  (Δ T P)  = Δ[ t ∶ T ] scROrn (σ S O) (P t)
scROrn         (σ S O)  (∇ s P)  = ∇ s (scROrn (O s) P)
scROrn         (Δ T O)  (σ .T P) = Δ[ t ∶ T ] scROrn (O t) (P t)
scROrn         (Δ T O)  (Δ T' P) = Δ[ t ∶ T' ] scROrn (Δ T O) (P t)
scROrn         (Δ T O)  (∇ t P)  = scROrn (O t) P
scROrn         (∇ s O)  P        = ∇ s (scROrn O P)
scROrn         (O * O') (Δ T P)  = Δ[ t ∶ T ] scROrn (O * O') (P t)
scROrn         (O * O') (P * P') = scROrn O P * scROrn O' P'

_⊙_ : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → Orn e D E → Orn f E F → Orn (e ∘ f) D F
_⊙_ {f = f} (wrap O) (wrap O') = wrap λ { {._} (ok k) → scROrn (O (ok (f k))) (O' (ok k)) }

shiftΔ : ∀ {I J K T} {e : J → I} {f : K → J} {D E F} → (O : ROrn e D E) (P : (t : T) → ROrn f E (F t)) →
         {X : I → Set} (xs : ⟦ σ T F ⟧ (X ∘ e ∘ f)) → erase (Δ T λ t → scROrn O (P t)) {X} xs ≡ erase (scROrn O (Δ T P)) xs
shiftΔ ∎        P (t , xs) = refl
shiftΔ (ṿ refl) P (t , xs) = refl
shiftΔ (O * O') P (t , xs) = refl
shiftΔ (σ S O)  P (t , xs) = refl
shiftΔ (Δ T O)  P (t , xs) = refl
shiftΔ (∇ s O)  P (t , xs) = cong (_,_ s) (shiftΔ O P (t , xs))

erase-after-erase : ∀ {I J K} {e : J → I} {f : K → J} {D E F} (O : ROrn e D E) (P : ROrn f E F) →
                    ∀ {X} (xs : ⟦ F ⟧ (X ∘ e ∘ f)) → erase (scROrn O P) {X} xs ≡ erase O {X} (erase P {X ∘ e} xs)
erase-after-erase         ∎        ∎           xs         = refl
erase-after-erase {e = e} ∎        (Δ T P) {X} (t , xs)   = erase-after-erase {e = e} ∎ (P t) {X} xs
erase-after-erase         (ṿ refl) (ṿ refl)    xs         = refl
erase-after-erase         (ṿ refl) (Δ T P) {X} (t , xs)   = erase-after-erase (ṿ refl) (P t) {X} xs
erase-after-erase         (σ S O)  (σ .S P)    (s , xs)   = cong (_,_ s) (erase-after-erase (O s) (P s) xs)
erase-after-erase         (σ S O)  (Δ T P)     (t , xs)   = erase-after-erase (σ S O) (P t) xs
erase-after-erase         (σ S O)  (∇ s P)     xs         = cong (_,_ s) (erase-after-erase (O s) P xs)
erase-after-erase         (Δ T O)  (σ .T P)    (t , xs)   = erase-after-erase (O t) (P t) xs
erase-after-erase         (Δ T O)  (Δ U P)     (u , xs)   = erase-after-erase (Δ T O) (P u) xs
erase-after-erase         (Δ T O)  (∇ t P)     xs         = erase-after-erase (O t) P xs
erase-after-erase         (∇ s O)  P           xs         = cong (_,_ s) (erase-after-erase O P xs)
erase-after-erase         (O * O') (Δ T P)     (t , xs)   = erase-after-erase (O * O') (P t) xs
erase-after-erase         (O * O') (P * P')    (xs , xs') = cong₂ _,_ (erase-after-erase O P xs) (erase-after-erase O' P' xs')

forget-after-forget :
  ∀ {I J K} {e : J → I} {f : K → J} {D E F} (O : Orn e D E) (P : Orn f E F) →
  ∀ {k} (x : μ F k) → forget (O ⊙ P) x ≡ forget O (forget P x)
forget-after-forget {e = e} {f} {D} {E} {F} O P =
  induction F (λ x → forget (O ⊙ P) x ≡ forget O (forget P x))
              (λ {i} fs all → cong con (aux (Orn.comp O (ok (f i))) (Orn.comp P (ok i)) fs all))
  where aux : ∀ {D' E' F'} (O' : ROrn e D' E') (P' : ROrn f E' F') →
              (fs : ⟦ F' ⟧ (μ F)) (all : All F' (λ x → forget (O ⊙ P) x ≡ forget O (forget P x)) fs) →
              erase (scROrn O' P') {μ D} (mapFold F F' (ornAlg (O ⊙ P)) fs)
                ≡ erase O' (mapFold E E' (ornAlg O) (erase P' (mapFold F F' (ornAlg P) fs)))
        aux ∎          ∎          fs         all          = refl
        aux ∎          (Δ T P')   (t , fs)   all          = aux ∎ (P' t) fs all
        aux (ṿ refl)   (ṿ refl)   fs         all          = all
        aux (ṿ refl)   (Δ T P')   (t , fs)   all          = aux (ṿ refl) (P' t) fs all -- change def'n of scROrn to avoid pattern match on idx
        aux (σ S O')   (σ .S P')  (s , fs)   all          = cong (_,_ s) (aux (O' s) (P' s) fs all)
        aux (σ S O')   (Δ T P')   (t , fs)   all          = aux (σ S O') (P' t) fs all
        aux (σ S O')   (∇ s P')   fs         all          = cong (_,_ s) (aux (O' s) P' fs all)
        aux (Δ T O')   (σ .T P')  (t , fs)   all          = aux (O' t) (P' t) fs all
        aux (Δ T O')   (Δ U P')   (u , fs)   all          = aux (Δ T O') (P' u) fs all
        aux (Δ T O')   (∇ t P')   fs         all          = aux (O' t) P' fs all
        aux (∇ s O')   P'         fs         all          = cong (_,_ s) (aux O' P' fs all)
        aux (O' * O'') (Δ T P')   (t , fs)   all          = aux (O' * O'') (P' t) fs all
        aux (O' * O'') (P' * P'') (fs , fs') (all , all') = cong₂ _,_ (aux O' P' fs all) (aux O'' P'' fs' all')

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
scROrn-cong-r {e = e} {e'} {f} {D} {._} {E} {F} refl Q O P oeq X xs xs' heq =
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
    aux : ∀ {E F} (Q : ROrn f E F) (xs : ⟦ F ⟧ (X ∘ e ∘ f)) (xs' : ⟦ F ⟧ (X ∘ e' ∘ f)) →
          HoriEq F xs F xs' → HoriEq E (erase Q {X ∘ e} xs) E (erase Q {X ∘ e'} xs')
    aux ∎        xs        xs'         heq          = ∎
    aux (ṿ refl) xs        xs'         (ṿ heq)      = ṿ heq
    aux (σ S Q)  (.s , xs) (.s , xs')  (σ s heq)    = σ s (aux (Q s) xs xs' heq)
    aux (Δ T Q)  (.t , xs) (.t , xs')  (σ t heq)    = aux (Q t) xs xs' heq
    aux (∇ s Q)  xs        xs'         heq          = σ s (aux Q xs xs' heq)
    aux (Q * R)  (xs , ys) (xs' , ys') (heq * heq') = aux Q xs xs' heq * aux R ys ys' heq'

⊙-cong-r : ∀ {I J K} {e e' : J → I} {f : K → J} {D E F}
           (Q : Orn f E F) (O : Orn e D E) (P : Orn e' D E) → OrnEq O P → OrnEq (O ⊙ Q) (P ⊙ Q)
⊙-cong-r {e = e} {e'} {f} {D} {E} {F} Q O P (eeq , oeq) =
  fcong-r f eeq ,
  λ k → scROrn-cong-r (cong (Desc.comp D) (eeq (f k))) (Orn.comp Q (ok k)) (Orn.comp O (ok (f k))) (Orn.comp P (ok (f k))) (oeq (f k))
