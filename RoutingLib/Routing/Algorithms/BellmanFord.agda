open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Vec using (Vec; []; _∷_; tabulate; foldr)
open import Induction.WellFounded using (Acc; acc)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Vec using (foldr₂)
open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule using (Schedule)
open import RoutingLib.Function using (_^_)

-- Distributed BellmanFord
module RoutingLib.Routing.Algorithms.BellmanFord
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) where

  open RoutingProblem rp

  I : RMatrix
  I i j with j ≟ᶠ i
  ... | yes _ = 1#
  ... | no  _ = 0#

  -- Algorithm for a single iteration
  σ : RMatrix → RMatrix
  σ X i j = foldr₂ _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

  -- A possible parallelisation of the algorithm where each 
  -- node is in charge of its own routes
  σ∥ : Parallelisation b ℓ n
  σ∥ = record 
    { Sᵢ = λ _ → Sₜ 
    ; σ = σ
    }

  open Parallelisation σ∥ using (δ; σ^) public
  open RoutingProblem rp using (RMatrix) public
