{-# OPTIONS --termination-depth=2 #-}
-- Can I rewrite path-len-induction to not require this?

open import Algebra using (Semiring)

open import Data.Fin using (Fin; zero; _≟_)
open import Data.List using (List; []; _∷_; [_]; length; map)
open import Data.List.All using (All; tabulate; _∷_; [])
open import Data.List.All.Properties using () renaming (map⁺ to allMap⁺)
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Properties using (map⁻; map⁺)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-concat⁺′; ∈-concat⁺; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; z≤n) renaming (_≟_ to _≟N_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; ≤∧≢⇒<)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; cong to ≡-cong; trans to ≡-trans)
open import Function using (_∘_)

open import RoutingLib.db716.Data.Path.UncertifiedFinite

module RoutingLib.db716.Data.Path.UncertifiedFinite.Properties where

all-all-k-length-paths-correct : ∀ {n k i vs} → length vs ≡ k → PathTo i vs → ValidPath vs → Any (vs ∈_) (all-all-k-length-paths-from-to n k i)
all-k-length-paths-to-correct : ∀ {n k i vs} → length vs ≡ k → PathTo i vs → ValidPath vs → vs ∈ all-k-length-paths-to n k i
all-k-length-paths-from-to-correct : ∀ {n k i j vs} → length vs ≡ k → PathFrom i vs → PathTo j vs → ValidPath vs →  vs ∈ all-k-length-paths-from-to n k i j

all-all-k-length-paths-correct {0} {k} {()}
all-all-k-length-paths-correct {suc n} {k} {i} {[]} |vs|≡k ()
all-all-k-length-paths-correct {suc n} {k} {i} {(r , s) ∷ vs} |vs|≡k vs:*→i valid = lose step2 step1
  where
    step1 : (r , s) ∷ vs ∈ all-k-length-paths-from-to (suc n) k r i
    step1 = all-k-length-paths-from-to-correct {suc n} {k} {r} {i} {(r , s) ∷ vs} |vs|≡k here vs:*→i valid
    
    lem : ∀ {n} r → r ∈ allFins n
    lem zero = here ≡-refl
    lem (Fin.suc r) = there (∈-map⁺ ? (lem r))
    
    step2 : all-k-length-paths-from-to (suc n) k r i ∈ all-all-k-length-paths-from-to (suc n) k i
    step2 = ∈-map⁺ ? (lem r)

all-k-length-paths-to-correct {ℕ.zero} {k} {()}
all-k-length-paths-to-correct {suc n} {k} {i} {vs} |vs|≡k vs:*→i valid = ∈-concat⁺ (all-all-k-length-paths-correct {suc n} {k} {i} {vs} |vs|≡k vs:*→i valid)

≡-pred : ∀ {a} {A : Set a} {l : ℕ} (x : A) (xs : List A) → length (x ∷ xs) ≡ (suc l) → length xs ≡ l
≡-pred {a} {A} {.(Data.List.foldr (λ _ → suc) 0 xs)} x xs ≡-refl = ≡-refl

ij⇿p⇒i▻p≡ij::p : ∀ {n} {i j : Fin n} {p : Path n} → 1 ≤ length p → (i , j) ⇿ p →  (i , j) ∷ p ≡ i ▻ p
ij⇿p⇒i▻p≡ij::p {n} {i} {j} {.[]} () start
ij⇿p⇒i▻p≡ij::p {n} {i} {j} {.((j , _) ∷ _)} 1≤p continue = ≡-refl


all-k-length-paths-from-to-correct {ℕ.zero} {k} {()}
all-k-length-paths-from-to-correct {suc n} {ℕ.zero} {i} {j} {.((i , _) ∷ _)} () here vs:*→j
all-k-length-paths-from-to-correct {suc n} {suc ℕ.zero} {i} {j} {.(i , _) ∷ []} |vs|≡k here (there ())
all-k-length-paths-from-to-correct {suc n} {suc ℕ.zero} {i} {j} {.(i , _) ∷ x ∷ p} () here (there vs:*→j)
all-k-length-paths-from-to-correct {suc n} {suc (suc k)} {_} {.s} {(_ , s) ∷ .[]} () here here

all-k-length-paths-from-to-correct {suc n} {suc ℕ.zero} {i} {j} {.((i , j) ∷ [])} |vs|≡k here here valid = here ≡-refl
all-k-length-paths-from-to-correct {suc n} {suc (suc k)} {i} {j} {(i , s) ∷ p} |vs|≡k here (there vs:*→j) (ve ∷ vp)
  rewrite (ij⇿p⇒i▻p≡ij::p (≤-trans (s≤s z≤n) (≤-reflexive (≡-sym (≡-pred (i , s) p |vs|≡k)))) ve ) =
  let
      -- z : Path (suc n)
      -- z∈all-all-paths : z ∈ map (λ i → all-k-length-paths-from-to (suc n) (suc k) i j) (allFins (suc n))
      -- p∈z : p ∈ z
      (z , z∈all-all-paths , p∈z) = find (all-all-k-length-paths-correct {suc n} {suc k} {j} {p} (≡-pred (i , s) p |vs|≡k) vs:*→j vp)
  in (∈-map⁺ ? (∈-concat⁺′ p∈z z∈all-all-paths))

all-≤k-length-paths-from-to-correct : ∀ {n k i j vs} → length vs ≤ k → PathFrom i vs → PathTo j vs → ValidPath vs →  vs ∈ all-≤k-length-paths-from-to n k i j

all-≤k-length-paths-from-to-correct {n} {ℕ.zero} {i} {j} {.((i , _) ∷ _)} () here
all-≤k-length-paths-from-to-correct {n} {suc k} {i} {j} {[]} |vs|≤k ()

all-≤k-length-paths-from-to-correct {n} {suc k} {i} {j} {vs} (s≤s |vs|≤k) here vs:*→j valid with length vs ≟N suc k
... | yes |vs|≡k =  ∈-++⁺ʳ (Path n) _ (all-k-length-paths-from-to-correct |vs|≡k here vs:*→j valid) 
... | no |vs|≢k = ∈-++⁺ˡ (Path n) (all-≤k-length-paths-from-to-correct (≤∧≢⇒< |vs|≤k (|vs|≢k ∘ (≡-cong suc))) here vs:*→j valid)

-- Lemma for induction over the lists returned by k-length-paths-from-to
path-len-induction : ∀ {a} (P : ∀ {n k} → Pred (Path n) a)
  → (∀ {n} → P {n} {0} [])
  → (∀ {n} i j → P {n} {1} ((i , j) ∷ []))
  → (∀ {n} {k} {xs} i → P {n} {k} xs → P {n} {suc k} (i ▻ xs))
  → ∀ n k xs i j → xs ∈ all-k-length-paths-from-to n k i j → P {n} {k} xs
  
path-len-induction P p[] p[ij] pxs⇒pi▻xs n k xs i j xs∈paths = k-length-paths-prop3 {n} k xs i j xs∈paths
  where
    
    k-length-paths-prop1 : ∀ {n} k (xs : Path n) (i : Fin n) → Any (xs ∈_) (all-all-k-length-paths-from-to n k i) → P {n} {k} xs
    k-length-paths-prop2 : ∀ {n} k (xs : Path n) (i : Fin n) → xs ∈ (all-k-length-paths-to n k i) → P {n} {k} xs
    k-length-paths-prop3 : ∀ {n} k (xs : Path n) (i j : Fin n) → xs ∈ (all-k-length-paths-from-to n k i j) → P {n} {k} xs

    k-length-paths-prop1 {0} k xs () xs∈l∈l'
    k-length-paths-prop1 {suc n} k xs j xs∈l∈l' =
      let xs∈l = map⁻ xs∈l∈l'
          i , i∈fins , xs∈paths = find xs∈l
      in k-length-paths-prop3 k xs i j xs∈paths
                                       
    k-length-paths-prop2 {0} k xs ()
    k-length-paths-prop2 {suc n} k xs i xs∈paths = k-length-paths-prop1 k xs i (∈-concat⁻ (all-all-k-length-paths-from-to (suc n) k i) xs∈paths)
      where open import Data.List.Membership.Propositional.Properties using (∈-concat⁻)

    k-length-paths-prop3 {0} k xs ()
    k-length-paths-prop3 {suc n} 0 [] i j xs∈paths = p[]
    k-length-paths-prop3 {suc n} 0 (x ∷ xs) i j xs∈paths with i ≟ j 
    k-length-paths-prop3 {suc n} 0 (x ∷ xs) i j (here ()) | yes i≡j
    k-length-paths-prop3 {suc n} 0 (x ∷ xs) i j (there ()) | yes i≡j
    k-length-paths-prop3 {suc n} 0 (x ∷ xs) i j () | no i≢j
    k-length-paths-prop3 {suc n} (suc 0) xs i j (here ≡-refl) = p[ij] i j
    k-length-paths-prop3 {suc n} (suc 0) xs i j (there ())
    k-length-paths-prop3 {suc n} (suc (suc k)) xs i j xs∈paths = ret
      where
        open import Data.List.Any.Properties using (map⁻)
        open import Relation.Binary
    
        mapPullback : Any (λ ys → xs ≡ i ▻ ys) (all-k-length-paths-to (suc n) (suc k) j)
        mapPullback = map⁻ xs∈paths

        tup : ∃ λ xs' → xs' ∈ (all-k-length-paths-to (suc n) (suc k) j) × xs ≡ i ▻ xs'
        tup = find mapPullback
      
        xs' : Path (suc n)
        xs' = proj₁ tup
  
        xs'∈paths : xs' ∈ all-k-length-paths-to (suc n) (suc k) j
        xs'∈paths = proj₁ (proj₂ tup)

        xs≡i▻xs' : xs ≡ i ▻ xs'
        xs≡i▻xs' = proj₂ (proj₂ tup)

        pxs' : P {suc n} {suc k} xs'
        pxs' = k-length-paths-prop2 (suc k) xs' j xs'∈paths

        ret : P {suc n} {suc (suc k)} xs
        ret rewrite xs≡i▻xs' = pxs⇒pi▻xs {suc n} {suc k} i pxs'

-- Lemma for induction over the lists returned by k-length-paths-from-to
path-len-induction' : ∀ {a} (P : ∀ {n k} {i j : Fin n} → Pred (Path n) a)
  → (∀ {n} i j → P {n} {1} {i} {j} ((i , j) ∷ []))
  → (∀ {n} {k} {i'} {j} {xs} i → P {n} {k} {i'} {j} xs → P {n} {suc k} {i} {j} (i ▻ xs))
  → ∀ n k xs i j → xs ∈ all-k-length-paths-from-to n (suc k) i j → P {n} {suc k} {i} {j} xs
  
path-len-induction' P p[ij] pxs⇒pi▻xs n k xs i j xs∈paths = k-length-paths-prop3 {n} k xs i j xs∈paths
  where
    
    k-length-paths-prop1 : ∀ {n} k (xs : Path n) (j : Fin n) → Any (xs ∈_) (all-all-k-length-paths-from-to n (suc k) j) → ∃ λ i → P {n} {suc k} {i} {j} xs
    k-length-paths-prop2 : ∀ {n} k (xs : Path n) (j : Fin n) → xs ∈ (all-k-length-paths-to n (suc k) j) → ∃ λ i → P {n} {suc k} {i} {j} xs
    k-length-paths-prop3 : ∀ {n} k (xs : Path n) (i j : Fin n) → xs ∈ (all-k-length-paths-from-to n (suc k) i j) → P {n} {suc k} {i} {j} xs

    k-length-paths-prop1 {0} k xs () xs∈l∈l'
    k-length-paths-prop1 {suc n} k xs j xs∈l∈l' =
      let xs∈l = map⁻ xs∈l∈l'
          i , i∈fins , xs∈paths = find xs∈l
      in  i , k-length-paths-prop3 k xs i j xs∈paths
                                       
    k-length-paths-prop2 {0} k xs ()
    k-length-paths-prop2 {suc n} k xs i xs∈paths = k-length-paths-prop1 k xs i (∈-concat⁻ (all-all-k-length-paths-from-to (suc n) (suc k) i) xs∈paths) 
      where open import Data.List.Membership.Propositional.Properties using (∈-concat⁻)

    k-length-paths-prop3 {0} k xs ()
    k-length-paths-prop3 {suc n} 0 xs i j (here ≡-refl) = p[ij] i j 
    k-length-paths-prop3 {suc n} 0 xs i j (there ())
    k-length-paths-prop3 {suc n} (suc k) xs i j xs∈paths = ret
      where
        open import Data.List.Any.Properties using (map⁻)
        open import Relation.Binary
    
        mapPullback : Any (λ ys → xs ≡ i ▻ ys) (all-k-length-paths-to (suc n) (suc k) j)
        mapPullback = map⁻ xs∈paths --xs∈paths

        tup : ∃ λ xs' → xs' ∈ (all-k-length-paths-to (suc n) (suc k) j) × xs ≡ i ▻ xs'
        tup = find mapPullback
      
        xs' : Path (suc n)
        xs' = proj₁ tup
  
        xs'∈paths : xs' ∈ all-k-length-paths-to (suc n) (suc k) j
        xs'∈paths = proj₁ (proj₂ tup)

        xs≡i▻xs' : xs ≡ i ▻ xs'
        xs≡i▻xs' = proj₂ (proj₂ tup)

        pxs' : ∃ λ i → P {suc n} {suc k} {i} {j} xs'
        pxs' = k-length-paths-prop2 k xs' j xs'∈paths

        ret : P {suc n} {suc (suc k)} {i} {j} xs
        ret rewrite xs≡i▻xs' = pxs⇒pi▻xs {suc n} {suc k} i (proj₂ pxs' )


addVertex-length : ∀ {n} (xs : Path n) (i : Fin n) → length (addVertex i xs) ≡ suc (length xs)
addVertex-length {n} [] i = ≡-refl 
addVertex-length {n} (x ∷ xs) i = ≡-refl

-- Proof that k-length paths have length k..
k-length-paths-length : ∀ {n} k (xs : Path n) (i j : Fin n) → xs ∈ (all-k-length-paths-from-to n k i j) → length xs ≡ k
k-length-paths-length {n} = path-len-induction
  (λ {_} {k} xs → length xs ≡ k)
  ≡-refl
  (λ _ _ → ≡-refl)
  (λ {n} {k} {xs} i |xs|≡k → ≡-trans (addVertex-length xs i) (≡-cong suc |xs|≡k)) n

addVertex-valid : ∀ {n} {xs : Path n} (i : Fin n) → ValidPath xs → ValidPath (addVertex i xs)
addVertex-valid {n} {[]} i xs-valid = start ∷ []
addVertex-valid {n} {x ∷ xs} i xs-valid = continue ∷ xs-valid

k-length-paths-valid : ∀ {n} k (xs : Path n) (i j : Fin n) → xs ∈ (all-k-length-paths-from-to n k i j) → ValidPath xs
k-length-paths-valid {n} =  path-len-induction ValidPath [] (λ i j → start ∷ []) addVertex-valid n 

k-length-paths-from-i : ∀ {n} k (i j : Fin n) → All (PathFrom i) (all-k-length-paths-from-to n (suc k) i j)
k-length-paths-from-i {ℕ.zero} k ()
k-length-paths-from-i {suc n} ℕ.zero i j = here ∷ []
k-length-paths-from-i {suc n} (suc k) i j = allMap⁺ (tabulate (λ { {[]} _ → here ; {x ∷ xs} _ → here}))

addVertexPreservesDest : ∀ {n} {j : Fin n} {xs : Path n} (i : Fin n) → PathTo j xs → PathTo j (i ▻ xs)
addVertexPreservesDest {n} {j} {(_ , j) ∷ []} i here = there here
addVertexPreservesDest {n} {j} {e ∷ p} i (there xs:*→j) = there (there xs:*→j)

k-length-paths-to-j : ∀ {n} k (xs : Path n) (i j : Fin n) → xs ∈ (all-k-length-paths-from-to n (suc k) i j) → PathTo j xs
k-length-paths-to-j {n} = path-len-induction' (λ {_} {_} {_} {j} → PathTo j) (λ i j → here) (λ {n} {_} {_} → addVertexPreservesDest {n}) n

i≡j⇒[]∈paths0 : ∀ n (i j : Fin n) → i ≡ j → [] ∈ all-k-length-paths-from-to n 0 i j
i≡j⇒[]∈paths0 ℕ.zero ()
i≡j⇒[]∈paths0 (suc n) i i ≡-refl with i ≟ i
... | yes _ = here ≡-refl
... | no i≢i = contradiction ≡-refl i≢i

paths≤k⊂paths≤k+1 : ∀ n k i j p → p ∈ all-≤k-length-paths-from-to n k i j → p ∈ all-≤k-length-paths-from-to n (suc k) i j
paths≤k⊂paths≤k+1 n k i j p p∈paths≤k = ∈-++⁺ˡ (Path n) p∈paths≤k

i≡j⇒[]∈paths≤k : ∀ n k (i j : Fin n) → i ≡ j → [] ∈ all-≤k-length-paths-from-to n k i j
i≡j⇒[]∈paths≤k ℕ.zero k ()
i≡j⇒[]∈paths≤k (suc n) ℕ.zero i i ≡-refl with i ≟ i
... | yes _ = here ≡-refl
... | no i≢i = contradiction ≡-refl i≢i
i≡j⇒[]∈paths≤k (suc n) (suc k) i .i ≡-refl = paths≤k⊂paths≤k+1 (suc n) k i i [] (i≡j⇒[]∈paths≤k (suc n) k i i ≡-refl) 
