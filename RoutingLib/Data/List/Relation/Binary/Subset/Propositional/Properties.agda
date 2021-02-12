open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.List.Base using (applyUpTo)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties

module RoutingLib.Data.List.Relation.Binary.Subset.Propositional.Properties where

module _ {a} {A : Set a} where

  -- stdlib
  applyUpTo⁺ : ∀ (f : ℕ → A) {m n} → m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  applyUpTo⁺ _ (s≤s m≤n) (here  f≡f[0]) = here f≡f[0]
  applyUpTo⁺ _ (s≤s m≤n) (there v∈xs)   = there (applyUpTo⁺ _ m≤n v∈xs)

