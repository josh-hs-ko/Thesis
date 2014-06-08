-- Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
-- Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
-- Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

module Ornament where

open import Prelude.Equality
open import Prelude.Function
open import Prelude.InverseImage
open import Prelude.Function.Fam
open import Description
open import Description.Horizontal

open import Function using (id; flip; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; curry) renaming (map to _**_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym; cong; cong₂; setoid; proof-irrelevance)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡) renaming (refl to hrefl)


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

Ė-trans-inv : {I J K : Set} {e : J → I} {f : K → J} {is : List I} {js : List J} {ks : List K} → Ė (e ∘ f) ks is → Ė f ks js → Ė e js is
Ė-trans-inv []         []            = []
Ė-trans-inv (eq ∷ eqs) (refl ∷ eqs') = eq ∷ Ė-trans-inv eqs eqs'

Ė-computation : {I J : Set} (e : J → I) (js : List J) → Ė e js (map e js)
Ė-computation e []       = []
Ė-computation e (j ∷ js) = refl ∷ Ė-computation e js

Ė-computation' : {I J : Set} (e : J → I) {is : List I} (js : List J) → is ≡ map e js → Ė e js is
Ė-computation' e js refl = Ė-computation e js

Ė-unique : {I J : Set} {e : J → I} {is : List I} {js : List J} → Ė e js is → is ≡ map e js
Ė-unique []           = refl
Ė-unique (refl ∷ eqs) = cong₂ _∷_ refl (Ė-unique eqs)

Ė-subst : {I J : Set} {e e' : J → I} {is : List I} {js : List J} → e ≐ e' → Ė e js is → Ė e' js is
Ė-subst eeq []               = []
Ė-subst eeq (_∷_ {j} eq eqs) = trans (sym (eeq j)) eq ∷ Ė-subst eeq eqs

Ė-irrelevance : {I J : Set} {e : J → I} {is : List I} {js : List J} → (eqs eqs' : Ė e js is) → eqs ≡ eqs'
Ė-irrelevance []         []                  = refl
Ė-irrelevance (eq ∷ eqs) (eq' ∷ eqs') with proof-irrelevance eq eq'
Ė-irrelevance (eq ∷ eqs) (.eq ∷ eqs') | refl = cong (_∷_ eq) (Ė-irrelevance eqs eqs')

data ROrn {I J : Set} (e : J → I) : RDesc I → RDesc J → Set₁ where
  ṿ   : {js : List J} {is : List I} (eqs : Ė e js is) → ROrn e (ṿ is) (ṿ js)
  σ   : (S : Set) {D : S → RDesc I} {E : S → RDesc J} (O : (s : S) → ROrn e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ   : (T : Set) {D : RDesc I} {E : T → RDesc J} (O : (t : T) → ROrn e D (E t)) → ROrn e D (σ T E)
  ∇   : {S : Set} (s : S) {D : S → RDesc I} {E : RDesc J} (O : ROrn e (D s) E) → ROrn e (σ S D) E

syntax σ S (λ s → O) = σ[ s ∈ S ] O
syntax Δ T (λ t → O) = Δ[ t ∈ T ] O

idROrn : {I : Set} (D : RDesc I) → ROrn id D D
idROrn (ṿ is)  = ṿ Ė-refl
idROrn (σ S D) = σ[ s ∈ S ] idROrn (D s)

Erasure : {I J : Set} (e : J → I) (Y : List J → Set) (X : List I → Set) → Set
Erasure {I} {J} e Y X = {is : List I} {js : List J} → Ė e js is → Y js → X is

{-

Erasure-comp : {I J K : Set} (e : J → I) (f : K → J) (Z : List K → Set) (Y : List J → Set) (X : List I → Set) →
               Erasure e Y X → Erasure f Z Y → Erasure (e ∘ f) Z X
Erasure-comp e f Z Y X g h {is} {ks} eqs z = g (Ė-trans-inv eqs (Ė-computation f ks)) (h (Ė-computation f ks) z)

-}

erase' : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E →
         {X : List I → Set} {Y : List J → Set} → Erasure e Y X → Ḣ E Y → Ḣ D X
erase' (ṿ eqs) f y        = f eqs y
erase' (σ S O) f (s , ys) = s , erase' (O s) f ys
erase' (Δ T O) f (t , ys) = erase' (O t) f ys
erase' (∇ s O) f ys       = s , erase' O f ys

erase-Ṡ : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → Ṡ E → Ṡ D
erase-Ṡ O = erase' O (const !)

erase-Ṗ : {I J : Set} {e : J → I} {X : I → Set} → Erasure e (flip Ṗ (X ∘ e)) (flip Ṗ X)
erase-Ṗ         []         _        = tt
erase-Ṗ {X = X} (eq ∷ eqs) (x , xs) = subst X eq x , erase-Ṗ eqs xs

ṖHEq : {I : Set} {X Y : I → Set} (is : List I) → Ṗ is X → Ṗ is Y → Set
ṖHEq is xs ys = All-Ṗ (λ _ xy → proj₁ xy ≅ proj₂ xy) is (Ṗ-comp is xs ys)

cong-erase-Ṗ :
  {I J : Set} {e e' : J → I} {is is' : List I} {js : List J} (eqs : Ė e js is) (eqs' : Ė e' js is') → is ≡ is' →
  {X : I → Set} (xs : Ṗ js (X ∘ e)) (xs' : Ṗ js (X ∘ e')) → ṖHEq js xs xs' → erase-Ṗ {X = X} eqs xs ≅ erase-Ṗ {X = X} eqs' xs'
cong-erase-Ṗ         []                 []            refl _        _          _                     = hrefl
cong-erase-Ṗ {e = e} (_∷_ {j} refl eqs) (refl ∷ eqs') iseq (x , xs) (x' , xs') (heq , heqs) with e j
cong-erase-Ṗ {e = e} (_∷_ {j} refl eqs) (refl ∷ eqs') refl (x , xs) (.x , xs') (hrefl , heqs) | ._   =
  ≡-to-≅ (cong (_,_ x) (≅-to-≡ (cong-erase-Ṗ eqs eqs' refl xs xs' heqs)))

erase : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → {X : I → Set} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
erase O = erase' O erase-Ṗ

erase-idROrn-Ṗ : {I : Set} {X : I → Set} (is : List I) (xs : Ṗ is X) → erase-Ṗ Ė-refl xs ≡ xs
erase-idROrn-Ṗ []       _        = refl
erase-idROrn-Ṗ (i ∷ is) (x , xs) = cong₂ _,_ refl (erase-idROrn-Ṗ is xs)

erase'-idROrn : {I : Set} (D : RDesc I) {X Y : List I → Set} (f : Erasure id Y X) (ys : Ḣ D Y) → erase' (idROrn D) f ys ≡ Ḣ-map D (f Ė-refl) ys
erase'-idROrn (ṿ is)  f ys       = refl
erase'-idROrn (σ S D) f (s , ys) = cong (_,_ s) (erase'-idROrn (D s) f ys)

record Orn {I J : Set} (e : J → I) (D : Desc I) (E : Desc J) : Set₁ where
  constructor wrap
  field
    comp : {i : I} (j : e ⁻¹ i) → ROrn e (Desc.comp D i) (Desc.comp E (und j))

idOrn : {I : Set} (D : Desc I) → Orn id D D
idOrn D = wrap λ { {._} (ok i) → idROrn (Desc.comp D i) }

-- ornamental algebra

ornAlg : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → Ḟ E (μ D ∘ e) ⇉ μ D ∘ e
ornAlg O {j} = con ∘ erase (Orn.comp O (ok j))

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
  ṿ   : {is : List I} (js : Ṗ is (InvImage e)) → ROrnDesc J e (ṿ is)
  σ   : (S : Set) {D : S → RDesc I} (O : (s : S) → ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  Δ   : (T : Set) {D : RDesc I} (O : T → ROrnDesc J e D) → ROrnDesc J e D
  ∇   : {S : Set} (s : S) {D : S → RDesc I} (O : ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)

record OrnDesc {I : Set} (J : Set) (e : J → I) (D : Desc I) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → ROrnDesc J e (Desc.comp D i)

Ṗ-toList : {I J : Set} {X : I → Set} → (X ⇉ const J) → (is : List I) → Ṗ is X → List J
Ṗ-toList f []        tt        = []
Ṗ-toList f (i ∷ is)  (x , xs)  = f x ∷ Ṗ-toList f is xs

und-Ṗ : {I J : Set} {e : J → I} (is : List I) → Ṗ is (InvImage e) → List J
und-Ṗ = Ṗ-toList und

toRDesc : {I J : Set} {e : J → I} {D : RDesc I} → ROrnDesc J e D → RDesc J
toRDesc (ṿ {is} js) = ṿ (und-Ṗ is js)
toRDesc (σ S O)     = σ[ s ∈ S ] toRDesc (O s)
toRDesc (Δ T O)     = σ[ t ∈ T ] toRDesc (O t)
toRDesc (∇ s O)     = toRDesc O

⌊_⌋ : {I J : Set} {e : J → I} {D : Desc I} → OrnDesc J e D → Desc J
⌊ wrap O ⌋ = wrap λ j → toRDesc (O (ok j))

to≡-Ṗ : {I J : Set} {e : J → I} (is : List I) (js : Ṗ is (InvImage e)) → Ė e (und-Ṗ is js) is
to≡-Ṗ []       _        = []
to≡-Ṗ (i ∷ is) (j , js) = to≡ j ∷ to≡-Ṗ is js

toROrn : {I J : Set} {e : J → I} {D : RDesc I} → (O : ROrnDesc J e D) → ROrn e D (toRDesc O)
toROrn (ṿ js)  = ṿ (to≡-Ṗ _ js)
toROrn (σ S O) = σ[ s ∈ S ] toROrn (O s)
toROrn (Δ T O) = Δ[ t ∈ T ] toROrn (O t)
toROrn (∇ s O) = ∇ s (toROrn O)

⌈_⌉ : {I J : Set} {e : J → I} {D : Desc I} → (O : OrnDesc J e D) → Orn e D ⌊ O ⌋
⌈ wrap O ⌉ = wrap λ { {._} (ok j) → toROrn (O (ok j)) }

idROrnDesc : ∀ {I} (D : RDesc I) → ROrnDesc I id D
idROrnDesc (ṿ is)  = ṿ (generate-Ṗ ok is)
idROrnDesc (σ S D) = σ[ s ∈ S ] idROrnDesc (D s)


--------
-- singleton ornaments

erode : {I : Set} (D : RDesc I) → {J : I → Set} → ⟦ D ⟧ J → ROrnDesc (Σ I J) proj₁ D
erode (ṿ is)  js         = ṿ (Ṗ-map (λ {i} j → ok (i , j)) is js)
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
