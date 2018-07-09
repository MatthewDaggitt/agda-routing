open import Data.Fin using (Fin)

open import RoutingLib.Relation.Unary.Indexed using (_∈_)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid)

open import RoutingLib.Asynchronous
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois1 as UresinDubois1
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3 as UresinDubois3
-- import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois4 as UresinDubois4
import RoutingLib.Asynchronous.Convergence.Proofs.Gurney6 as Gurney6

module RoutingLib.Asynchronous.Convergence.Theorems
  {a ℓ n} {S : Setoid (Fin n) a ℓ}
  {P : Parallelisation S} where

------------------------------------------------------------------------
-- Export core publically
open import RoutingLib.Asynchronous.Convergence.Conditions public
open Parallelisation P

open ACO
-- open FiniteConditions
open SynchronousConditions

------------------------------------------------------------------------
-- ACO implications

ACO⇒partiallySafe : ∀ {ℓ} (aco : ACO P ℓ) → IsPartiallyAsynchronouslySafe P (D aco 0)
ACO⇒partiallySafe aco = isPartiallyAsynchronouslySafe
  where open UresinDubois1 P aco using (isPartiallyAsynchronouslySafe)

------------------------------------------------------------------------
-- Ultrametric conditions implications

ultra⇒ACO : UltrametricConditions P → ACO P _
ultra⇒ACO ultra = aco
  where open Gurney6 ultra using (aco)

ultra⇒safe : UltrametricConditions P → IsAsynchronouslySafe P
ultra⇒safe ultra = partialToTotalSafety x∈D[0] (ACO⇒partiallySafe (ultra⇒ACO ultra)) 
  where open Gurney6 ultra using (x∈D[0])

------------------------------------------------------------------------
-- Synchronous conditions implications

-- The second proof is a little more complicated as U&D's construction
-- of the ACO has a set D(0) that we can only guarantee contains a
-- single x₀ out of the original D₀

sync⇒ACO : ∀ {ℓ₁ ℓ₂} (sync : SynchronousConditions P ℓ₁ ℓ₂) → ∀ {x} → x ∈ D₀ sync → ACO P _
sync⇒ACO sync = aco
  where open UresinDubois3 P sync using (aco)

sync⇒safe : ∀ {ℓ₁ ℓ₂} (sync : SynchronousConditions P ℓ₁ ℓ₂) → IsPartiallyAsynchronouslySafe P (D₀ sync)
sync⇒safe sync = record
  { m*         = ξ sync
  ; m*-reached = λ x∈D₀ → IsPartiallyAsynchronouslySafe.m*-reached (ACO⇒partiallySafe (sync⇒ACO sync x∈D₀)) (x₀∈D[0] x∈D₀)
  }
  where
  open SynchronousConditions sync
  open UresinDubois3 P sync using (x₀∈D[0])

------------------------------------------------------------------------
-- Finite conditions

-- These are still a work in progress after U&D initial conditions
-- turned out to be not strong enough.

{-
finite⇒ACO : ∀ {ℓ} → FiniteConditions P ℓ → ACO P ℓ
finite⇒ACO finite = aco
  where open UresinDubois4 P finite

finite⇒safe : ∀ {ℓ} (fin : FiniteConditions P ℓ) → IsPartiallyAsynchronouslySafe P (FiniteConditions.D₀ fin)
finite⇒safe finite = ACO⇒partiallySafe {!aco!}
  where open UresinDubois4 P finite
-}
