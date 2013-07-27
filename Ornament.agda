-- Definition of ornaments, i.e., a universe for simple, structural natural transformations between functors decoded from descriptions.
-- Ornamental descriptions are provided for constructing new descriptions from old ones such that ornaments can be automatically derived.
-- Singleton ornaments are also defined, which create as many singleton types as there are elements of the base type.

module Ornament where

open import Prelude.Equality
open import Prelude.InverseImage
open import Prelude.Function.Fam
open import Description

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; setoid)


--------
-- ornaments

data ROrn {I J} (e : J → I) : RDesc I → RDesc J → Set₁ where
  ∎   : ROrn e ∎ ∎
  ṿ   : ∀ {j i} (idx : e j ≡ i) → ROrn e (ṿ i) (ṿ j)
  σ   : (S : Set) → ∀ {D E} (O : ∀ s → ROrn e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ   : (T : Set) → ∀ {D E} (O : ∀ t → ROrn e D (E t)) → ROrn e D (σ T E)
  ∇   : {S : Set} (s : S) → ∀ {D E} (O : ROrn e (D s) E) → ROrn e (σ S D) E
  _*_ : ∀ {D E} (O : ROrn e D E) → ∀ {D' E'} (O' : ROrn e D' E') → ROrn e (D * D') (E * E')

syntax σ S (λ s → O) = σ[ s ∶ S ] O
syntax Δ T (λ t → O) = Δ[ t ∶ T ] O

erase : ∀ {I J} {e : J → I} {D E} → ROrn e D E → ∀ {X} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
erase ∎        _        = tt
erase (ṿ refl) x        = x
erase (σ S O)  (s , xs) = s , erase (O s) xs
erase (Δ T O)  (t , xs) = erase (O t) xs
erase (∇ s O)  xs       = s , erase O xs
erase (O * O') (x , x') = erase O x , erase O' x'

idROrn : ∀ {I} (D : RDesc I) → ROrn id D D
idROrn ∎       = ∎
idROrn (ṿ i)   = ṿ refl
idROrn (σ S D) = σ[ s ∶ S ] idROrn (D s)
idROrn (D * E) = idROrn D * idROrn E

erase-idROrn : ∀ {I} (D : RDesc I) → ∀ {X} {xs : ⟦ D ⟧ X} → erase (idROrn D) xs ≡ xs
erase-idROrn ∎                       = refl
erase-idROrn (ṿ i)                   = refl
erase-idROrn (σ S D) {xs = s , xs  } = cong (_,_ s) (erase-idROrn (D s))
erase-idROrn (D * E) {xs = xs , xs'} = cong₂ _,_ (erase-idROrn D) (erase-idROrn E)

record Orn {I J : Set} (e : J → I) (D : Desc I) (E : Desc J) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → ROrn e (D at i) (E at und j)

idOrn : ∀ {I} (D : Desc I) → Orn id D D
idOrn D = wrap λ { {._} (ok i) → idROrn (D at i) }

-- ornamental algebra

ornAlg : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → Ḟ E (μ D ∘ e) ⇉ μ D ∘ e
ornAlg {D = D} (wrap O) {j} = con ∘ erase (O (ok j))

forget : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → μ E ⇉ μ D ∘ e
forget O = fold (ornAlg O)

forget-idOrn : ∀ {I} {D : Desc I} → ∀ {i} (x : μ D i) → forget (idOrn D) x ≡ x
forget-idOrn {I} {D} = induction D (λ x → forget (idOrn D) x ≡ x) (λ {i} xs all → cong con (aux (D at i) xs all))
  where aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) (all : All D' (λ x → forget (idOrn D) x ≡ x) xs) →
              erase (idROrn D') (mapFold D D' (ornAlg (idOrn D)) xs) ≡ xs
        aux ∎         xs         all          = refl
        aux (ṿ i)     xs         all          = all
        aux (σ S D')  (s , xs)   all          = cong (_,_ s) (aux (D' s) xs all)
        aux (D' * E') (xs , xs') (all , all') = cong₂ _,_ (aux D' xs all) (aux E' xs' all')


--------
-- ornamental descriptions

data ROrnDesc {I : Set} (J : Set) (e : J → I) : RDesc I → Set₁ where
  ∎   : ROrnDesc J e ∎
  ṿ   : ∀ {i} (j : e ⁻¹ i) → ROrnDesc J e (ṿ i)
  σ   : (S : Set) → ∀ {D} (O : ∀ s → ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  Δ   : (T : Set) → ∀ {D} (O : T → ROrnDesc J e D) → ROrnDesc J e D
  ∇   : {S : Set} (s : S) → ∀ {D} (O : ROrnDesc J e (D s)) → ROrnDesc J e (σ S D)
  _*_ : ∀ {D} (O : ROrnDesc J e D) → ∀ {D'} (O' : ROrnDesc J e D') → ROrnDesc J e (D * D')

record OrnDesc {I : Set} (J : Set) (e : J → I) (D : Desc I) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → ROrnDesc J e (D at i)

toRDesc : ∀ {I J} {e : J → I} {D} → ROrnDesc J e D → RDesc J
toRDesc ∎             = ∎
toRDesc (ṿ (ok j))    = ṿ j
toRDesc (σ S O)       = σ[ s ∶ S ] toRDesc (O s)
toRDesc (Δ T O)       = σ[ t ∶ T ] toRDesc (O t)
toRDesc (∇ s O)       = toRDesc O
toRDesc (O * O')      = toRDesc O * toRDesc O'

⌊_⌋ : ∀ {I J} {e : J → I} {D} → OrnDesc J e D → Desc J
⌊ wrap O ⌋ = wrap λ j → toRDesc (O (ok j))

toROrn : ∀ {I J} {e : J → I} {D} → (O : ROrnDesc J e D) → ROrn e D (toRDesc O)
toROrn ∎          = ∎
toROrn (ṿ (ok j)) = ṿ refl
toROrn (σ S O)    = σ[ s ∶ S ] toROrn (O s)
toROrn (Δ T O)    = Δ[ t ∶ T ] toROrn (O t)
toROrn (∇ s O)    = ∇ s (toROrn O)
toROrn (O * O')   = toROrn O * toROrn O'

⌈_⌉ : ∀ {I J} {e : J → I} {D} → (O : OrnDesc J e D) → Orn e D ⌊ O ⌋
⌈ wrap O ⌉ = wrap λ { {._} (ok j) → toROrn (O (ok j)) }

idROrnDesc : ∀ {I} (D : RDesc I) → ROrnDesc I id D
idROrnDesc ∎       = ∎
idROrnDesc (ṿ i)   = ṿ (ok i)
idROrnDesc (σ S D) = σ[ s ∶ S ] idROrnDesc (D s)
idROrnDesc (D * E) = idROrnDesc D * idROrnDesc E


--------
-- singleton ornaments

erode : ∀ {I} (D : RDesc I) → ∀ {J} → ⟦ D ⟧ J → ROrnDesc (Σ I J) proj₁ D
erode ∎       _          = ∎
erode (ṿ i)   j          = ṿ (ok (i , j))
erode (σ S D) (s , js)   = ∇ s (erode (D s) js)
erode (D * E) (js , js') = erode D js * erode E js'

singOrn : ∀ {I} (D : Desc I) → OrnDesc (Σ I (μ D)) proj₁ D
singOrn D = wrap λ { {._} (ok (i , con ds)) → erode (D at i) ds }

singleton-aux :
  ∀ {I} {D : Desc I} (D' : RDesc I)
  (xs : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} x → μ ⌊ singOrn D ⌋ (i , x)) xs) → ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋)
singleton-aux ∎         xs          all         = tt
singleton-aux (ṿ i)     xs          all         = all
singleton-aux (σ S D')  (s , xs)    all         = singleton-aux (D' s) xs all
singleton-aux (D' * E') (xs , xs') (all , all') = singleton-aux D' xs all , singleton-aux E' xs' all'

singleton-alg :
  ∀ {I} (D : Desc I) {i : I} (xs : Ḟ D (μ D) i) → All (D at i) (λ {i} x → μ ⌊ singOrn D ⌋ (i , x)) xs → μ ⌊ singOrn D ⌋ (i , con xs)
singleton-alg D {i} xs all = con (singleton-aux (D at i) xs all)

singleton : ∀ {I} {D : Desc I} → ∀ {i} (x : μ D i) → μ ⌊ singOrn D ⌋ (i , x)
singleton {D = D} = induction D (λ {i} x → μ ⌊ singOrn D ⌋ (i , x)) (singleton-alg D)

singleton-unique : ∀ {I} {D : Desc I} → ∀ {i} (x : μ D i) → Unique (setoid _) (singleton x)
singleton-unique {I} {D} =
  induction D (λ x → Unique (setoid _) (singleton x)) (λ { {i} xs all (con ys) → cong con (aux (D at i) xs all ys) })
  where aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) (all : All D' (λ x → Unique (setoid _) (singleton x)) xs)
              (ys : ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋)) →
              singleton-aux D' xs (everywhereInduction D D' (λ {i} x → μ ⌊ singOrn D ⌋ (i , x)) (singleton-alg D) xs) ≡ ys
        aux ∎         xs         all          ys         = refl
        aux (ṿ i)     x          all          y          = all y
        aux (σ S D')  (s , xs)   all          ys         = aux (D' s) xs all ys
        aux (D' * E') (xs , xs') (all , all') (ys , ys') = cong₂ _,_ (aux D' xs all ys) (aux E' xs' all' ys')

forget-singOrn : ∀ {I} {D : Desc I} → ∀ {i} {x : μ D i} (s : μ ⌊ singOrn D ⌋ (i , x)) → forget ⌈ singOrn D ⌉ s ≡ x
forget-singOrn {I} {D} =
  induction ⌊ singOrn D ⌋ (λ { {i , x} s → forget ⌈ singOrn D ⌉ s ≡ x }) (λ { {i , con xs} ss all → cong con (aux (D at i) xs ss all) })
  where aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) (ss : ⟦ toRDesc (erode D' xs) ⟧ (μ ⌊ singOrn D ⌋))
              (all : All (toRDesc (erode D' xs)) (λ { {i , x} s → forget ⌈ singOrn D ⌉ {i , x} s ≡ x }) ss) →
              erase (toROrn (erode D' xs)) (mapFold ⌊ singOrn D ⌋ (toRDesc (erode D' xs)) (λ {ix} → ornAlg ⌈ singOrn D ⌉ {ix}) ss) ≡ xs
        aux ∎         xs         ss         all          = refl
        aux (ṿ i)     xs         ss         all          = all
        aux (σ S D')  (s , xs)   ss         all          = cong (_,_ s) (aux (D' s) xs ss all)
        aux (D' * E') (xs , xs') (ss , ss') (all , all') = cong₂ _,_ (aux D' xs ss all) (aux E' xs' ss' all')
