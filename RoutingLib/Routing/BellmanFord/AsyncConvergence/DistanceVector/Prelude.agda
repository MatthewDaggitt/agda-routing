open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Product using (∃; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.List using (List; length)
open import Function using (flip)

open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.FiniteStrictlyIncreasingRoutingAlgebra
 as FiniteStrictlyIncreasingRoutingAlgebraProperties
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
open FiniteStrictlyIncreasingRoutingAlgebra using (Step)

module RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude
  {a b ℓ n}
  (algebra : FiniteStrictlyIncreasingRoutingAlgebra a b ℓ)
  (A : SquareMatrix (Step algebra) n)
  where

  open FiniteStrictlyIncreasingRoutingAlgebra algebra public
  open FiniteStrictlyIncreasingRoutingAlgebraProperties algebra public
  
  open BellmanFord rawRoutingAlgebra A public
  open BellmanFordProperties routingAlgebra A public
