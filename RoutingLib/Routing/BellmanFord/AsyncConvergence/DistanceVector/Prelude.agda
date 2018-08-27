open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Data.Product using (∃; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.List using (List; length)
open import Function using (flip)

open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra using (AdjacencyMatrix)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties

module RoutingLib.Routing.BellmanFord.AsyncConvergence.DistanceVector.Prelude
  {a b ℓ n}
  {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (A : AdjacencyMatrix algebra n)
  where

  open RawRoutingAlgebra algebra public
  open IsRoutingAlgebra isRoutingAlgebra public
  
  open BellmanFord algebra A public
  open BellmanFordProperties algebra isRoutingAlgebra A public
