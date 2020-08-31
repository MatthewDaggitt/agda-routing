import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; map; tabulate)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary using (TotalOrder)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict

module RoutingLib.Data.List.Extrema
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

open import Data.List.Extrema totalOrder

open TotalOrder totalOrder

max-mono-⊆ : ∀ {⊥₁ ⊥₂ xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊆ ys → max ⊥₁ xs ≤ max ⊥₂ ys
max-mono-⊆ ⊥₁≤⊥₂ xs⊆ys = max[xs]≤max[ys]⁺ _ _ (inj₁ ⊥₁≤⊥₂)
  (tabulate (inj₂ ∘ Any.map (reflexive ∘ Eq.reflexive) ∘ xs⊆ys))
