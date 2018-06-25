open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (foldr; tabulate)
open import Data.Product using (_×_)
open import Relation.Binary using (Setoid; DecSetoid)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.DecidableEquality as TableDecEquality
open import RoutingLib.Data.Matrix
import RoutingLib.Data.Matrix.Relation.DecidableEquality as MatrixDecEquality

open import RoutingLib.Routing.Algebra


module RoutingLib.Routing.BellmanFord
  {a b ℓ n}
  (𝓡𝓐 : RawRoutingAlgebra a b ℓ)
  (A : SquareMatrix (RawRoutingAlgebra.Step 𝓡𝓐) n)
  where
  
open RawRoutingAlgebra 𝓡𝓐
--------------------------------------------------------------------------------
-- Definitions

Node : Set
Node = Fin n

Edge : Set
Edge = Fin n × Fin n

open MatrixDecEquality DS public
open TableDecEquality DS using (𝕋ₛ)

RTable : Set b
RTable = Table Route n

RMatrix : Set b
RMatrix = SquareMatrix Route n

ℝ𝕋ₛ : Setoid b ℓ
ℝ𝕋ₛ = 𝕋ₛ n

ℝ𝕄ₛ : Setoid b ℓ
ℝ𝕄ₛ = 𝕄ₛ n n

Decℝ𝕄ₛ : DecSetoid b ℓ
Decℝ𝕄ₛ = Dec𝕄ₛ n n

--------------------------------------------------------------------------------
-- Algorithm

-- Identity matrix
I : RMatrix
I i j with j ≟ᶠ i
... | yes _ = 0#
... | no  _ = ∞

-- Single iteration
σ : RMatrix → RMatrix
σ X i j = foldr _⊕_ (I i j) (tabulate (λ k → A i k ▷ X k j))

-- Multiple iterations
σ^ : ℕ → RMatrix → RMatrix
σ^ zero    X = X
σ^ (suc t) X = σ (σ^ t X)

-- Parallelisation of algorithm
σ∥ : Parallelisation (λ _ → ℝ𝕋ₛ)
σ∥ = record { F = σ }

open Parallelisation σ∥ using () renaming (asyncIter to δ) public
