open import Data.Bool using (true; false; if_then_else_)
open import Data.List.Base as List hiding (head; tail)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Linked using ([]; [-]; _∷_)
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as Sorted
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Binary.Permutation.Propositional
import Data.List.Relation.Binary.Permutation.Propositional.Properties as Perm
open import Data.Maybe.Base using (just)
open import Relation.Nullary using (does)
open import Data.Nat using (_<_; _>_; z≤n; s≤s)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤-step)
open import Data.Product as Prod using (_,_; proj₁)
open import Function.Base using (_∘_; id)
open import Relation.Binary using (Rel; Decidable; DecTotalOrder)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≗_)

open import RoutingLib.Data.Maybe.Relation.Binary.Connected

module RoutingLib.Data.List.Sort.MergeSort
  {a ℓ₁ ℓ₂} (O : DecTotalOrder a ℓ₁ ℓ₂) where

open DecTotalOrder O renaming (Carrier to A)

open import RoutingLib.Data.List.Sort.Base totalOrder
open import Data.List.Relation.Unary.Sorted.TotalOrder totalOrder hiding (head; tail)

private
  open import Relation.Binary.Properties.DecTotalOrder O using (≰⇒>)
  
  ≰⇒≥ : ∀ {x y} → ¬ (x ≤ y) → y ≤ x
  ≰⇒≥ x≰y = proj₁ (≰⇒> x≰y)
  
  tail : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
  tail [-]       = []
  tail (_ ∷ Rxs) = Rxs

  head′ : ∀ {x xs} → Sorted (x ∷ xs) → Connected _≤_ (just x) (List.head xs)
  head′ [-]       = just-nothing
  head′ (Rxy ∷ _) = just Rxy
  
  infixr 5 _∷′_
  _∷′_ : ∀ {x xs} →
         Connected _≤_ (just x) (List.head xs) →
         Sorted xs →
         Sorted (x ∷ xs)
  _∷′_ {xs = []}     _  _            = [-]
  _∷′_ {xs = y ∷ xs} (just Rxy) Ryxs = Rxy ∷ Ryxs

open PermutationReasoning


------------------------------------------------------------------------
-- Definition

merge : ∀ {ℓ} {R : Rel A ℓ} → Decidable R → List A → List A → List A
merge R? []       ys       = ys
merge R? xs       []       = xs
merge R? (x ∷ xs) (y ∷ ys) = if does (R? x y)
  then x ∷ merge R? xs (y ∷ ys)
  else y ∷ merge R? (x ∷ xs) ys

mergePairs : List (List A) → List (List A)
mergePairs (xs ∷ ys ∷ xss) = merge _≤?_ xs ys ∷ mergePairs xss
mergePairs xss             = xss

private
  length-mergePairs : ∀ xs ys xss → length (mergePairs (xs ∷ ys ∷ xss)) < length (xs ∷ ys ∷ xss)
  length-mergePairs _ _ []              = s≤s (s≤s z≤n)
  length-mergePairs _ _ (xss ∷ [])      = s≤s (s≤s (s≤s z≤n))
  length-mergePairs _ _ (xs ∷ ys ∷ xss) = s≤s (≤-step (length-mergePairs xs ys xss))

mergeAll : (xss : List (List A)) → Acc _<_ (length xss) → List A
mergeAll []        _               = []
mergeAll (xs ∷ []) _               = xs
mergeAll (xs ∷ ys ∷ xss) (acc rec) = mergeAll
  (mergePairs (xs ∷ ys ∷ xss)) (rec _ (length-mergePairs xs ys xss))

sort : List A → List A
sort xs = mergeAll (map [_] xs) (<-wellFounded _)

------------------------------------------------------------------------
-- Permutation property

concat-[-] : concat {A = A} ∘ map [_] ≗ id
concat-[-] [] = P.refl
concat-[-] (x ∷ xs) = P.cong (x ∷_) (concat-[-] xs)

merge-↭ : ∀ xs ys → merge _≤?_ xs ys ↭ xs ++ ys
merge-↭ []       []       = ↭-refl
merge-↭ []       (y ∷ ys) = ↭-refl
merge-↭ (x ∷ xs) []       = ↭-sym (Perm.++-identityʳ (x ∷ xs))
merge-↭ (x ∷ xs) (y ∷ ys)
  with does (x ≤? y) | merge-↭ xs (y ∷ ys) | merge-↭ (x ∷ xs) ys
... | true  | rec | _   = prep x rec
... | false | _   | rec = begin
  y ∷ merge _≤?_ (x ∷ xs) ys <⟨ rec ⟩
  y ∷ x ∷ xs ++ ys           ↭˘⟨ Perm.shift y (x ∷ xs) ys ⟩
  (x ∷ xs) ++ y ∷ ys         ≡˘⟨ ++-assoc [ x ] xs (y ∷ ys) ⟩
  x ∷ xs ++ y ∷ ys           ∎
  where open PermutationReasoning

mergePairs-↭ : ∀ xss → concat (mergePairs xss) ↭ concat xss
mergePairs-↭ []              = ↭-refl
mergePairs-↭ (xs ∷ [])       = ↭-refl
mergePairs-↭ (xs ∷ ys ∷ xss) = begin
  merge _ xs ys ++ concat (mergePairs xss) ↭⟨ Perm.++⁺ (merge-↭ xs ys) (mergePairs-↭ xss) ⟩
  (xs ++ ys)    ++ concat xss              ≡⟨ ++-assoc xs ys (concat xss) ⟩
  xs ++ ys      ++ concat xss              ∎

mergeAll-↭ : ∀ xss (rec : Acc _<_ (length xss)) → mergeAll xss rec ↭ concat xss
mergeAll-↭ []              _ = ↭-refl
mergeAll-↭ (xs ∷ [])       _ = ↭-sym (Perm.++-identityʳ xs)
mergeAll-↭ (xs ∷ ys ∷ xss) (acc rec) = begin
  mergeAll (mergePairs (xs ∷ ys ∷ xss)) _ ↭⟨ mergeAll-↭ (mergePairs (xs ∷ ys ∷ xss)) _ ⟩
  concat   (mergePairs (xs ∷ ys ∷ xss))   ↭⟨ mergePairs-↭ (xs ∷ ys ∷ xss) ⟩
  concat   (xs ∷ ys ∷ xss)                ∎

sort-↭ : ∀ xs → sort xs ↭ xs
sort-↭ xs = begin
  mergeAll (map [_] xs) _ ↭⟨ mergeAll-↭ (map [_] xs) _ ⟩
  concat (map [_] xs)     ≡⟨ concat-[-] xs ⟩
  xs                      ∎

------------------------------------------------------------------------
-- Sorted property

private
  merge-con : ∀ {v xs ys} →
              Connected _≤_ (just v) (List.head xs) →
              Connected _≤_ (just v) (List.head ys) →
              Connected _≤_ (just v) (List.head (merge _≤?_ xs ys))
  merge-con {xs = []}     {[]}     cxs cys = cys
  merge-con {xs = []}     {y ∷ ys} cxs cys = cys
  merge-con {xs = x ∷ xs} {[]}     cxs cys = cxs
  merge-con {xs = x ∷ xs} {y ∷ ys} cxs cys with x ≤? y
  ... | yes x≤y = cxs
  ... | no  x≰y = cys

merge⁺ : ∀ {xs ys} → Sorted xs → Sorted ys → Sorted (merge _≤?_ xs ys)
merge⁺ {[]}     {[]}     rxs rys = []
merge⁺ {[]}     {x ∷ ys} rxs rys = rys
merge⁺ {x ∷ xs} {[]}     rxs rys = rxs
merge⁺ {x ∷ xs} {y ∷ ys} rxs rys with x ≤? y |
  merge⁺ (tail rxs) rys | merge⁺ rxs (tail rys)
... | yes x≤y | rec | _   = merge-con (head′ rxs)      (just x≤y)  ∷′ rec
... | no  x≰y | _   | rec = merge-con (just (≰⇒≥ x≰y)) (head′ rys) ∷′ rec

mergePairs-↗ : ∀ {xss} → All Sorted xss → All Sorted (mergePairs xss)
mergePairs-↗ []                 = []
mergePairs-↗ (xs↗ ∷ [])         = xs↗ ∷ []
mergePairs-↗ (xs↗ ∷ ys↗ ∷ xss↗) = merge⁺ xs↗ ys↗ ∷ mergePairs-↗ xss↗

mergeAll-↗ : ∀ {xss} (rec : Acc _<_ (length xss)) →
             All Sorted xss → Sorted (mergeAll xss rec)
mergeAll-↗ rec       []                 = []
mergeAll-↗ rec       (xs↗ ∷ [])         = xs↗
mergeAll-↗ (acc rec) (xs↗ ∷ ys↗ ∷ xss↗) = mergeAll-↗ _ (mergePairs-↗ (xs↗ ∷ ys↗ ∷ xss↗))

sort-↗ : ∀ xs → Sorted (sort xs)
sort-↗ xs = mergeAll-↗ _ (All.map⁺ (All.universal (λ _ → [-]) xs))

------------------------------------------------------------------------
-- Algorithm

mergeSort : SortingAlgorithm
mergeSort = record
  { sort   = sort
  ; sort-↭ = sort-↭
  ; sort-↗ = sort-↗
  }
