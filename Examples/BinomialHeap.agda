-- Okasaki's idea of numerical representations are nicely captured by the coherence property of upgrades;
-- insertion into binomial heaps is used as an example.

open import Relation.Nullary using (Dec; yes; no)

module Examples.BinomialHeap (Val : Set) (_≤_ : Val → Val → Set) (_≤?_ : (x y : Val) → Dec (x ≤ y)) where

open import Prelude.Function
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament
open import Ornament.RefinementSemantics

open import Function using (_∘_; flip)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


--------
-- binary numbers

data BinTag : Set where
  `nil  : BinTag
  `zero : BinTag
  `one  : BinTag

BinD : Desc ⊤
BinD = wrap λ _ → σ BinTag λ { `nil  → ṿ []
                             ; `zero → ṿ (tt ∷ [])
                             ; `one  → ṿ (tt ∷ []) }

Bin : Set
Bin = μ BinD tt


--------
-- binomial trees

descend : ℕ → List ℕ
descend zero    = []
descend (suc n) = n ∷ descend n

BTreeD : Desc ℕ
BTreeD = wrap λ r → σ[ _ ∈ Val ] ṿ (descend r)

BTree : ℕ → Set
BTree = μ BTreeD

link : {r : ℕ} → BTree r → BTree r → BTree (suc r)
link (con (x , ts)) (con (y , us)) with x ≤? y
link (con (x , ts)) (con (y , us)) | yes _ = con (x , con (y , us) , ts)
link (con (x , ts)) (con (y , us)) | no  _ = con (y , con (x , ts) , us)

left : {r : ℕ} → BTree (suc r) → BTree r
left (con (x , t , ts)) = t

right : {r : ℕ} → BTree (suc r) → BTree r
right (con (x , t , ts)) = con (x , ts)


--------
-- binomial heaps

BHeapOD : OrnDesc ℕ ! BinD
BHeapOD = wrap λ { {._} (ok r) → σ BinTag λ { `nil  → ṿ tt
                                            ; `zero → ṿ (ok (suc r) , tt)
                                            ; `one  → Δ[ _ ∈ BTree r ] ṿ (ok (suc r) , tt) } }

BHeap : ℕ → Set
BHeap = μ ⌊ BHeapOD ⌋

toBin : {r : ℕ} → BHeap r → Bin
toBin = forget ⌈ BHeapOD ⌉

BHeap' : ℕ → Bin → Set
BHeap' r b = OptP ⌈ BHeapOD ⌉ (ok r) b


--------
-- increment and insertion

incr : Bin → Bin
incr (con (`nil  , _    )) = con (`one , con (`nil , tt) , tt)
incr (con (`zero , b , _)) = con (`one , b , tt)
incr (con (`one  , b , _)) = con (`zero , incr b , tt)

upg : Upgrade (Bin → Bin) ({r : ℕ} → BTree r → BHeap r → BHeap r)
upg = ∀⁺[[ r ∈ ℕ ]] ∀⁺[ _ ∈ BTree r ] let ref = FRefinement.comp (RSem' ⌈ BHeapOD ⌉) (ok r) in ref ⇀ toUpgrade ref

insT' : {r : ℕ} → BTree r → (b : Bin) → BHeap' r b → BHeap' r (incr b)  -- Upgrade.P upg incr
insT' t (con (`nil  , _    )) h                 = con (t , con tt               , tt)
insT' t (con (`zero , b , _)) (con (    h , _)) = con (t , h                    , tt)
insT' t (con (`one  , b , _)) (con (u , h , _)) = con (    insT' (link t u) b h , tt)

insT : {r : ℕ} → BTree r → BHeap r → BHeap r
insT = Upgrade.u upg incr insT'

incr-insT-coherence : {r : ℕ} (t : BTree r) (b : Bin) (h : BHeap r) → toBin h ≡ b → toBin (insT t h) ≡ incr b  -- Upgrade.C upg incr insT
incr-insT-coherence = Upgrade.c upg incr insT'

insert : Val → BHeap 0 → BHeap 0
insert x = insT (con (x , tt))


--------
-- addition and merging

add : Bin → Bin → Bin
add (con (`nil  , _    )) b'                     = b'
add (con (`zero , b , _)) (con (`nil  , _     )) = con (`zero , b               , tt)
add (con (`zero , b , _)) (con (`zero , b' , _)) = con (`zero , add b b'        , tt)
add (con (`zero , b , _)) (con (`one  , b' , _)) = con (`one  , add b b'        , tt)
add (con (`one  , b , _)) (con (`nil  , _     )) = con (`one  , b               , tt)
add (con (`one  , b , _)) (con (`zero , b' , _)) = con (`one  , add b b'        , tt)
add (con (`one  , b , _)) (con (`one  , b' , _)) = con (`zero , incr (add b b') , tt)

upg' : Upgrade (Bin → Bin → Bin) ({r : ℕ} → BHeap r → BHeap r → BHeap r)
upg' = ∀⁺[[ r ∈ ℕ ]] let ref = FRefinement.comp (RSem' ⌈ BHeapOD ⌉) (ok r) in ref ⇀ ref ⇀ toUpgrade ref

merge' : {r : ℕ} → (b : Bin) → BHeap' r b → (b' : Bin) → BHeap' r b' → BHeap' r (add b b')  -- Upgrade.P upg' add
merge' (con (`nil  , _    )) h                 b'                     h'                 = h'
merge' (con (`zero , b , _)) (con (    h , _)) (con (`nil  , _     )) h'                 = con (    h                                     , tt)
merge' (con (`zero , b , _)) (con (    h , _)) (con (`zero , b' , _)) (con (    h' , _)) = con (    merge' _ h _ h'                       , tt)
merge' (con (`zero , b , _)) (con (    h , _)) (con (`one  , b' , _)) (con (u , h' , _)) = con (u , merge' _ h _ h'                       , tt)
merge' (con (`one  , b , _)) (con (t , h , _)) (con (`nil  , _     )) h'                 = con (t , h                                     , tt)
merge' (con (`one  , b , _)) (con (t , h , _)) (con (`zero , b' , _)) (con (    h' , _)) = con (t , merge' _ h _ h'                       , tt)
merge' (con (`one  , b , _)) (con (t , h , _)) (con (`one  , b' , _)) (con (u , h' , _)) = con (    insT' (link t u) _ (merge' b h b' h') , tt)

merge : {r : ℕ} → BHeap r → BHeap r → BHeap r
merge = Upgrade.u upg' add merge'

add-merge-coherence :
  {r : ℕ} →
  (b  : Bin) (h  : BHeap r) → toBin h  ≡ b  →
  (b' : Bin) (h' : BHeap r) → toBin h' ≡ b' → toBin (merge h h') ≡ add b b'  -- Upgrade.C upg' add merge
add-merge-coherence = Upgrade.c upg' add merge'


--------
-- shifting and halving

shift : Bin → Bin
shift (con (`nil  ,     _)) = con (`nil , tt)
shift (con (`zero , b , _)) = b
shift (con (`one  , b , _)) = b

upg'' : Upgrade (Bin → Bin) (({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} → BHeap r → BHeap r)
upg'' = ∀⁺[ _ ∈ ({r : ℕ} → BTree (suc r) → BTree r) ]
        ∀⁺[[ r ∈ ℕ ]] let ref = FRefinement.comp (RSem' ⌈ BHeapOD ⌉) (ok r) in ref ⇀ toUpgrade ref

mapBHeap' : ({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} {b : Bin} → BHeap' (suc r) b → BHeap' r b
mapBHeap' f {r} {con (`nil  , _)} _                 = con tt
mapBHeap' f {r} {con (`zero , _)} (con (    h , _)) = con (      mapBHeap' f h , tt)
mapBHeap' f {r} {con (`one  , _)} (con (t , h , _)) = con (f t , mapBHeap' f h , tt)

halve' : ({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} (b : Bin) → BHeap' r b → BHeap' r (shift b)  -- Upgrade.P upg'' shift
halve' f (con (`nil  , _)) _                 = con tt
halve' f (con (`zero , _)) (con (    h , _)) = mapBHeap' f h
halve' f (con (`one  , _)) (con (t , h , _)) = mapBHeap' f h

halve : ({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} → BHeap r → BHeap r
halve = Upgrade.u upg'' shift halve'

shift-halve-coherence : (f : {r : ℕ} → BTree (suc r) → BTree r) {r : ℕ} (b : Bin) (h : BHeap r) →
                        toBin h ≡ b → toBin (halve f h) ≡ shift b  -- Upgrade.C upg'' shift halve
shift-halve-coherence = Upgrade.c upg'' shift halve'

{- The externalist approach:

shift : Bin → Bin
shift (con (`nil  ,     _)) = con (`nil , tt)
shift (con (`zero , b , _)) = b
shift (con (`one  , b , _)) = b

mapBHeap : ({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} → BHeap (suc r) → BHeap r
mapBHeap f (con (`nil  ,         _)) = con (`nil  ,                      tt)
mapBHeap f (con (`zero ,     h , _)) = con (`zero ,       mapBHeap f h , tt)
mapBHeap f (con (`one  , t , h , _)) = con (`one  , f t , mapBHeap f h , tt)

toBin-mapBHeap : (f : {r : ℕ} → BTree (suc r) → BTree r) {r : ℕ} (h : BHeap (suc r)) → toBin (mapBHeap f h) ≡ toBin h
toBin-mapBHeap f (con (`nil  ,         _)) = refl
toBin-mapBHeap f (con (`zero ,     h , _)) = cong con (cong (_,_ `zero) (cong (flip _,_ tt) (toBin-mapBHeap f h)))
toBin-mapBHeap f (con (`one  , t , h , _)) = cong con (cong (_,_ `one ) (cong (flip _,_ tt) (toBin-mapBHeap f h)))

halve : ({r : ℕ} → BTree (suc r) → BTree r) → {r : ℕ} → BHeap r → BHeap r
halve f (con (`nil  ,         _)) = con (`nil , tt)
halve f (con (`zero ,     h , _)) = mapBHeap f h
halve f (con (`one  , t , h , _)) = mapBHeap f h

shift-halve-coherence : (f : {r : ℕ} → BTree (suc r) → BTree r) {r : ℕ} (b : Bin) (h : BHeap r) →
                        toBin h ≡ b → toBin (halve f h) ≡ shift b
shift-halve-coherence f .(con (`nil  ,           _)) (con (`nil  ,         _)) refl = refl
shift-halve-coherence f .(con (`zero , toBin h , _)) (con (`zero ,     h , _)) refl = toBin-mapBHeap f h
shift-halve-coherence f .(con (`one  , toBin h , _)) (con (`one  , t , h , _)) refl = toBin-mapBHeap f h

-}
