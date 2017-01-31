open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Vec using (Vec; []; _∷_; allFin; map; foldr)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Function using (_^_)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Synchronous
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) where

  open RoutingProblem rp

  -- Identity matrix
  I : RMatrix
  I i j with j ≟ᶠ i
  ... | yes _ = 1#
  ... | no  _ = 0#

  -- All the possible ways of forming paths from i to j
  -- by extending the paths held in the current RMatrix
  extensions : RMatrix → Fin n → Fin n → Vec Route n
  extensions X i j = map (λ k → A i k ▷ X k j) (allFin n)

  -- One update iteration
  σ : RMatrix → RMatrix
  σ X i j = foldr (λ _ → Route) _⊕_ (I i j) (extensions X i j)

  -- Multiple update iterations
  σ^ : ℕ → RMatrix → RMatrix
  σ^ n = σ ^ n
