open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.List using (applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Relation.Subset.Propositional

module RoutingLib.Data.List.Relation.Binary.Subset.Propositional.Properties where

module _ {a} {A : Set a} where

  applyUpTo⁺ : ∀ (f : ℕ → A) {m n} → m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  applyUpTo⁺ _ z≤n       ()
  applyUpTo⁺ _ (s≤s m≤n) (here  f≡f[0]) = here f≡f[0]
  applyUpTo⁺ _ (s≤s m≤n) (there v∈xs)   = there (applyUpTo⁺ _ m≤n v∈xs)

