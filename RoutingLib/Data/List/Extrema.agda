open import Data.List.Any as Any using (Any; here; there)
open import Data.List.All using (All; []; _∷_; lookup; map; tabulate)
open import Data.List.Relation.Subset.Propositional using (_⊆_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (TotalOrder; Setoid)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst) renaming (refl to ≡-refl)

module RoutingLib.Data.List.Extrema
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

open import Data.List.Extrema totalOrder

open TotalOrder totalOrder renaming (Carrier to B)
open NonStrictToStrict _≈_ _≤_ using (_<_)

max-mono-⊆ : ∀ {⊥₁} {⊥₂} {xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊆ ys → max ⊥₁ xs ≤ max ⊥₂ ys
max-mono-⊆ {⊥₁} {⊥₂} {xs} {ys} ⊥₁≤⊥₂ xs⊆ys = max[xs]≤max[ys]⁺ {⊥₁} ⊥₂ {xs} ys (inj₁ ⊥₁≤⊥₂)
  (tabulate λ x∈xs → inj₂ (Any.map (λ {≡-refl → refl}) (xs⊆ys x∈xs)))
