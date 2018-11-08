open import Data.Fin using (Fin)
open import Data.Fin.Subset using (⊤)
open import Data.Product using (_,_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

open import RoutingLib.Relation.Unary.Indexed using (_∈_)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.ACOToSafe as ACOToSafe
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.UltrametricToACO as UltrametricToACO


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems where

------------------------------------------------------------------------
-- Export core publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-convergent : ∀ {a ℓ} (𝓘 : AsyncIterable a ℓ 0) → Convergent 𝓘
|0|-convergent p = record
  { x*         = λ _ _ ()
  ; x*-fixed   = λ _ _ ()
  ; x*-reached = λ _ _ → 0 , λ _ _ ()
  }

------------------------------------------------------------------------
-- Asynchronously contracting operators (ACOs)

module _ {a ℓ n} {𝓘 : AsyncIterable a ℓ n} where

  ACO⇒convergent : ∀ {p} (aco : ACO 𝓘 p) → ConvergentOver 𝓘 (ACO.B₀ aco)
  ACO⇒convergent aco = ACOToSafe.isSafe 𝓘 aco

------------------------------------------------------------------------
-- Ultrametric conditions

module _ {a ℓ n} {𝓘 : AsyncIterable a ℓ n} where

  ultra⇒ACO : UltrametricConditions 𝓘 → ACO 𝓘 ℓ
  ultra⇒ACO ultra = UltrametricToACO.aco ultra

  ultra⇒convergent : UltrametricConditions 𝓘 → Convergent 𝓘
  ultra⇒convergent ultra = convergentOver-universal
    (UltrametricToACO.B₀-univ ultra)
    (ACO⇒convergent (ultra⇒ACO ultra))

------------------------------------------------------------------------
-- Synchronous conditions implications

-- The second proof is a little more complicated as U&D's construction
-- of the ACO has a set D(0) that we can only guarantee contains a
-- single x₀ out of the original D₀

{-
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
-}

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
