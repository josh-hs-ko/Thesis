-- Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
-- Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
-- Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

module Thesis.Ornament where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function.Fam
open import Thesis.Description

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; curry)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym; cong; cong₂; setoid)


--------
-- ornaments

data Ė {I J : Set} (e : J → I) : List J → List I → Set where
  []  : Ė e [] []
  _∷_ : {j : J} {i : I} (eq : e j ≡ i) {js : List J} {is : List I} (eqs : Ė e js is) → Ė e (j ∷ js) (i ∷ is)

Ė-refl : {I : Set} {is : List I} → Ė id is is
Ė-refl {is = []    } = []
Ė-refl {is = i ∷ is} = refl ∷ Ė-refl {is = is}

Ė-trans : {I J K : Set} {e : J → I} {f : K → J} {is : List I} {js : List J} {ks : List K} → Ė e js is → Ė f ks js → Ė (e ∘ f) ks is
Ė-trans         []           []           = []
Ė-trans {e = e} (eeq ∷ eeqs) (feq ∷ feqs) = trans (cong e feq) eeq ∷ Ė-trans eeqs feqs

Ė-subst : {I J : Set} {e e' : J → I} {is : List I} {js : List J} → e ≐ e' → Ė e js is → Ė e' js is
Ė-subst eeq []               = []
Ė-subst eeq (_∷_ {j} eq eqs) = trans (sym (eeq j)) eq ∷ Ė-subst eeq eqs

data ROrn {I J : Set} (e : J → I) : RDesc I → RDesc J → Set₁ where
  ṿ   : {js : List J} {is : List I} (eqs : Ė e js is) → ROrn e (ṿ is) (ṿ js)
  σ   : (S : Set) → ∀ {D E} (O : ∀ s → ROrn e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ   : (T : Set) → ∀ {D E} (O : ∀ t → ROrn e D (E t)) → ROrn e D (σ T E)
  ∇   : {S : Set} (s : S) → ∀ {D E} (O : ROrn e (D s) E) → ROrn e (σ S D) E

syntax σ S (λ s → O) = σ[ s ∶ S ] O
syntax Δ T (λ t → O) = Δ[ t ∶ T ] O

idROrn : {I : Set} (D : RDesc I) → ROrn id D D
idROrn (ṿ is)  = ṿ Ė-refl
idROrn (σ S D) = σ[ s ∶ S ] idROrn (D s)

erase' : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E →
         {X : List I → Set} {Y : List J → Set} → ({is : List I} {js : List J} → Ė e js is → Y js → X is) → Ḣ E Y → Ḣ D X
erase' (ṿ eqs) f y        = f eqs y
erase' (σ S O) f (s , ys) = s , erase' (O s) f ys
erase' (Δ T O) f (t , ys) = erase' (O t) f ys
erase' (∇ s O) f ys       = s , erase' O f ys

erase-Ṁ : {I J : Set} {e : J → I} {js : List J} {is : List I} {X : I → Set} → Ė e js is → Ṁ (X ∘ e) js → Ṁ X is
erase-Ṁ         []         _        = tt
erase-Ṁ {X = X} (eq ∷ eqs) (x , xs) = subst X eq x , erase-Ṁ eqs xs

erase : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → {X : I → Set} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
erase O = erase' O erase-Ṁ

erase-idROrn-Ṁ : {I : Set} {X : I → Set} (is : List I) (xs : Ṁ X is) → erase-Ṁ Ė-refl xs ≡ xs
erase-idROrn-Ṁ []       _        = refl
erase-idROrn-Ṁ (i ∷ is) (x , xs) = cong₂ _,_ refl (erase-idROrn-Ṁ is xs)

erase-idROrn : ∀ {I} (D : RDesc I) → ∀ {X} {xs : ⟦ D ⟧ X} → erase (idROrn D) xs ≡ xs
erase-idROrn (ṿ is)  {xs = xs    } = erase-idROrn-Ṁ is xs
erase-idROrn (σ S D) {xs = s , xs} = cong (_,_ s) (erase-idROrn (D s))

record Orn {I J : Set} (e : J → I) (D : Desc I) (E : Desc J) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → ROrn e (Desc.comp D i) (Desc.comp E (und j))

idOrn : {I : Set} (D : Desc I) → Orn id D D
idOrn D = wrap λ { {._} (ok i) → idROrn (Desc.comp D i) }

-- ornamental algebra

ornAlg : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → Ḟ E (μ D ∘ e) ⇉ μ D ∘ e
ornAlg {D = D} O {j} = con ∘ erase (Orn.comp O (ok j))

forget : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → μ E ⇉ μ D ∘ e
forget O = fold (ornAlg O)

forget-idOrn : ∀ {I} {D : Desc I} → ∀ {i} (x : μ D i) → forget (idOrn D) x ≡ x
forget-idOrn {I} {D} = induction D (λ _ x → forget (idOrn D) x ≡ x) (λ i xs ihs → cong con (aux (Desc.comp D i) xs ihs))
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) → All D' (λ _ x → forget (idOrn D) x ≡ x) xs →
          erase (idROrn D') (mapFold D D' (ornAlg (idOrn D)) xs) ≡ xs
    aux (ṿ [])       _        _          = refl
    aux (ṿ (i ∷ is)) (x , xs) (ih , ihs) = cong₂ _,_ ih (aux (ṿ is) xs ihs)
    aux (σ S D')     (s , xs) ihs        = cong (_,_ s) (aux (D' s) xs ihs)

--------
-- ornamental descriptions

data ROrnDesc {I : Set} (J : Set) (e : J → I) : RDesc I → Set₁ where
  ṿ   : {is : List I} (js : Ṁ (InvImage e) is) → ROrnDesc J e (ṿ is)
  σ   : (S : Set) → ∀ {D} (O : ∀ s → ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  Δ   : (T : Set) → ∀ {D} (O : T → ROrnDesc J e D) → ROrnDesc J e D
  ∇   : {S : Set} (s : S) → ∀ {D} (O : ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)

record OrnDesc {I : Set} (J : Set) (e : J → I) (D : Desc I) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → ROrnDesc J e (Desc.comp D i)

und-Ṁ : {I J : Set} {e : J → I} (is : List I) → Ṁ (InvImage e) is → List J
und-Ṁ []       _        = []
und-Ṁ (i ∷ is) (j , js) = und j ∷ und-Ṁ is js

toRDesc : {I J : Set} {e : J → I} {D : RDesc I} → ROrnDesc J e D → RDesc J
toRDesc (ṿ js)  = ṿ (und-Ṁ _ js)
toRDesc (σ S O) = σ[ s ∶ S ] toRDesc (O s)
toRDesc (Δ T O) = σ[ t ∶ T ] toRDesc (O t)
toRDesc (∇ s O) = toRDesc O

⌊_⌋ : {I J : Set} {e : J → I} {D : Desc I} → OrnDesc J e D → Desc J
⌊ wrap O ⌋ = wrap λ j → toRDesc (O (ok j))

to≡-Ṁ : {I J : Set} {e : J → I} (is : List I) (js : Ṁ (InvImage e) is) → Ė e (und-Ṁ is js) is
to≡-Ṁ []       _        = []
to≡-Ṁ (i ∷ is) (j , js) = to≡ j ∷ to≡-Ṁ is js

toROrn : {I J : Set} {e : J → I} {D : RDesc I} → (O : ROrnDesc J e D) → ROrn e D (toRDesc O)
toROrn (ṿ js)  = ṿ (to≡-Ṁ _ js)
toROrn (σ S O) = σ[ s ∶ S ] toROrn (O s)
toROrn (Δ T O) = Δ[ t ∶ T ] toROrn (O t)
toROrn (∇ s O) = ∇ s (toROrn O)

⌈_⌉ : {I J : Set} {e : J → I} {D : Desc I} → (O : OrnDesc J e D) → Orn e D ⌊ O ⌋
⌈ wrap O ⌉ = wrap λ { {._} (ok j) → toROrn (O (ok j)) }

idROrnDesc : ∀ {I} (D : RDesc I) → ROrnDesc I id D
idROrnDesc (ṿ is)  = ṿ (generate-Ṁ ok is)
idROrnDesc (σ S D) = σ[ s ∶ S ] idROrnDesc (D s)


--------
-- singleton ornaments

erode : {I : Set} (D : RDesc I) → {J : I → Set} → ⟦ D ⟧ J → ROrnDesc (Σ I J) proj₁ D
erode (ṿ is)  js         = ṿ (Ṁ-map (λ {i} j → ok (i , j)) is js)
erode (σ S D) (s , js)   = ∇ s (erode (D s) js)

singOrn : {I : Set} (D : Desc I) → OrnDesc (Σ I (μ D)) proj₁ D
singOrn D = wrap λ { {._} (ok (i , con ds)) → erode (Desc.comp D i) ds }

singleton-aux :
  {I : Set} {D : Desc I} (D' : RDesc I)
  (xs : ⟦ D' ⟧ (μ D)) (ihs : All D' (λ i x → μ ⌊ singOrn D ⌋ (i , x)) xs) → ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋)
singleton-aux (ṿ [])       _        _          = tt
singleton-aux (ṿ (i ∷ is)) (x , xs) (ih , ihs) = ih , singleton-aux (ṿ is) xs ihs
singleton-aux (σ S D')     (s , xs) ihs        = singleton-aux (D' s) xs ihs

singleton-alg :
  {I : Set} (D : Desc I) (i : I) (xs : Ḟ D (μ D) i) → All (Desc.comp D i) (λ i x → μ ⌊ singOrn D ⌋ (i , x)) xs → μ ⌊ singOrn D ⌋ (i , con xs)
singleton-alg D i xs ihs = con (singleton-aux (Desc.comp D i) xs ihs)

singleton : {I : Set} {D : Desc I} {i : I} (x : μ D i) → μ ⌊ singOrn D ⌋ (i , x)
singleton {D = D} = induction D (λ i x → μ ⌊ singOrn D ⌋ (i , x)) (singleton-alg D)

singleton-unique : {I : Set} {D : Desc I} → {i : I} (x : μ D i) → Unique (setoid _) (singleton x)
singleton-unique {I} {D} =
  induction D (λ _ x → Unique (setoid _) (singleton x)) (λ { i xs ihs (con ys) → cong con (aux (Desc.comp D i) xs ihs ys) })
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) → All D' (λ _ x → Unique (setoid _) (singleton x)) xs →
          (ys : ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋)) →
          singleton-aux D' xs (everywhereInduction D D' (λ i x → μ ⌊ singOrn D ⌋ (i , x)) (singleton-alg D) xs) ≡ ys
    aux (ṿ [])       _        _          _        = refl
    aux (ṿ (i ∷ is)) (x , xs) (ih , ihs) (y , ys) = cong₂ _,_ (ih y) (aux (ṿ is) xs ihs ys)
    aux (σ S D')     (s , xs) ihs        ys       = aux (D' s) xs ihs ys

forget-singOrn : ∀ {I} {D : Desc I} → ∀ {i} {x : μ D i} (s : μ ⌊ singOrn D ⌋ (i , x)) → forget ⌈ singOrn D ⌉ s ≡ x
forget-singOrn {I} {D} =
  induction ⌊ singOrn D ⌋ (λ { (i , x) s → forget ⌈ singOrn D ⌉ s ≡ x }) (λ { (i , con xs) ss ihs → cong con (aux (Desc.comp D i) xs ss ihs) })
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) (ss : ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋)) →
          All (toRDesc (erode D' xs)) (λ { (i , x) s → forget ⌈ singOrn D ⌉ {i , x} s ≡ x }) ss →
          erase (toROrn (erode D' xs)) (mapFold ⌊ singOrn D ⌋ (toRDesc (erode D' xs)) (λ {ix} → ornAlg ⌈ singOrn D ⌉ {ix}) ss) ≡ xs
    aux (ṿ [])       _        _        _          = refl
    aux (ṿ (i ∷ is)) (x , xs) (s , ss) (ih , ihs) = cong₂ _,_ ih (aux (ṿ is) xs ss ihs)
    aux (σ S D')     (s , xs) ss       ihs        = cong (_,_ s) (aux (D' s) xs ss ihs)
