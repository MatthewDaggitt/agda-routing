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

open import RoutingLib.Data.List.AllPairs using ([]; _∷_) renaming (AllPairs to AllPairsₗ)

module RoutingLib.Data.Vec.All.Properties where


  -- All & fromList

  module _ {a p} {A : Set a} {P : A → Set p} where

    -- stdlib
    All-fromList⁺ : ∀ {xs} → Allₗ P xs → All P (fromList xs)
    All-fromList⁺ []         = []
    All-fromList⁺ (px ∷ pxs) = px ∷ All-fromList⁺ pxs

    -- stdlib
    All-fromList⁻ : ∀ {xs} → All P (fromList xs) → Allₗ P xs
    All-fromList⁻ {[]}     []         = []
    All-fromList⁻ {x ∷ xs} (px ∷ pxs) = px ∷ (All-fromList⁻ pxs)



  -- All & toList

  module _ {a p} {A : Set a} {P : A → Set p} where

    -- stdlib
    All-toList⁺ : ∀ {n} {xs : Vec A n} → Allₗ P (toList xs) → All P xs
    All-toList⁺ {xs = []}     []         = []
    All-toList⁺ {xs = x ∷ xs} (px ∷ pxs) = px ∷ All-toList⁺ pxs

    -- stdlib
    All-toList⁻ : ∀ {n} {xs : Vec A n} → All P xs → Allₗ P (toList xs)
    All-toList⁻ [] = []
    All-toList⁻ (px ∷ pxs) = px ∷ All-toList⁻ pxs
