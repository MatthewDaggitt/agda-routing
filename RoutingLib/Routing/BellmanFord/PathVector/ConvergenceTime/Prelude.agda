open import Data.Nat using (ℕ)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord as BellmanFord
import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions.Properties
  as SufficientConditionsProperties
import RoutingLib.Routing.BellmanFord.PathVector.Consistency as Consistency

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where
  
  open RoutingProblem 𝓡𝓟 public
  open BellmanFord 𝓡𝓟 public
  open PathSufficientConditions 𝓟𝓢𝓒 public
  open SufficientConditionsProperties 𝓟𝓢𝓒 public
  open Consistency 𝓟𝓢𝓒 public

  𝕋 : Set
  𝕋 = ℕ
