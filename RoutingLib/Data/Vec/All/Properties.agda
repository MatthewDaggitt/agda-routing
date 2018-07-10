open import Data.Vec as Vec
open import Data.Vec.All using (All; []; _∷_) renaming (map to mapₐ; lookup to lookupₐ)
open import Data.Vec.Relation.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Fin using (Fin; _<_) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (zero; suc; s≤s)
open import Data.List using ([]; _∷_)
open import Data.List.All using ([]; _∷_) renaming (All to Allₗ)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary using (Rel; _⇒_)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Vec.All using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.AllPairs using ([]; _∷_) renaming (AllPairs to AllPairsₗ)

module RoutingLib.Data.Vec.All.Properties where

  AllPairs-lookup : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} {n} {xs : Vec A n} →
                    AllPairs _~_ xs → ∀ {i j} → i < j → lookup i xs ~ lookup j xs
  AllPairs-lookup [] {()}
  AllPairs-lookup (x~xs ∷ pxs) {_}      {fzero}  ()
  AllPairs-lookup (x~xs ∷ pxs) {fzero}  {fsuc j} (s≤s i<j) = lookupₐ j x~xs
  AllPairs-lookup (x~xs ∷ pxs) {fsuc i} {fsuc j} (s≤s i<j) = AllPairs-lookup pxs i<j



  -- All & fromList

  module _ {a p} {A : Set a} {P : A → Set p} where

    All-fromList⁺ : ∀ {xs} → Allₗ P xs → All P (fromList xs)
    All-fromList⁺ []         = []
    All-fromList⁺ (px ∷ pxs) = px ∷ All-fromList⁺ pxs

    All-fromList⁻ : ∀ {xs} → All P (fromList xs) → Allₗ P xs
    All-fromList⁻ {[]}     []         = []
    All-fromList⁻ {x ∷ xs} (px ∷ pxs) = px ∷ (All-fromList⁻ pxs)

  -- AllPairs & fromList

  module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

    AllPairs-fromList⁺ : ∀ {xs} → AllPairsₗ _~_ xs → AllPairs _~_ (fromList xs)
    AllPairs-fromList⁺ [] = []
    AllPairs-fromList⁺ (px ∷ pxs) = (All-fromList⁺ px) ∷ (AllPairs-fromList⁺ pxs)



  -- All & toList

  module _ {a p} {A : Set a} {P : A → Set p} where

    All-toList⁺ : ∀ {n} {xs : Vec A n} → Allₗ P (toList xs) → All P xs
    All-toList⁺ {xs = []}     []         = []
    All-toList⁺ {xs = x ∷ xs} (px ∷ pxs) = px ∷ All-toList⁺ pxs

    All-toList⁻ : ∀ {n} {xs : Vec A n} → All P xs → Allₗ P (toList xs)
    All-toList⁻ [] = []
    All-toList⁻ (px ∷ pxs) = px ∷ All-toList⁻ pxs
