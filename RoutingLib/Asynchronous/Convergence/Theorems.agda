open import Relation.Binary using (Setoid)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Table using (Table)

import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois1 as UresinDubois1
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3 as UresinDubois3
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois4 as UresinDubois4
import RoutingLib.Asynchronous.Convergence.Proofs.Gurney6 as Gurney6

module RoutingLib.Asynchronous.Convergence.Theorems
  {a ℓ n} {S : Table (Setoid a ℓ) n}
  {P : Parallelisation S} where

  -- Export core publically
  open import RoutingLib.Asynchronous.Convergence.Conditions public
  open Parallelisation P using (_∈_)

  open ACO
  -- open FiniteConditions
  open SynchronousConditions

  -- ACO implications

  ACO⇒partiallySafe : ∀ {p} (aco : ACO P p) → IsPartiallyAsynchronouslySafe P (D aco 0)
  ACO⇒partiallySafe aco = isPartiallyAsynchronouslySafe
    where open UresinDubois1 P aco using (isPartiallyAsynchronouslySafe)

  -- Ultrametric conditions implications
  
  ultra⇒ACO : UltrametricConditions P → ACO P _
  ultra⇒ACO ultra = aco
    where open Gurney6 ultra using (aco)

  ultra⇒safe : UltrametricConditions P → IsAsynchronouslySafe P
  ultra⇒safe ultra = partialToTotalSafety x∈D[0] (ACO⇒partiallySafe (ultra⇒ACO ultra)) 
    where open Gurney6 ultra using (x∈D[0])

    
  -- Synchronous conditions implications

  sync⇒ACO : ∀ {ℓ} (sync : SynchronousConditions P ℓ) → ∀ {x} → x ∈ D₀ sync → ACO P ℓ
  sync⇒ACO sync = aco
    where open UresinDubois3 P sync using (aco)

  sync⇒safe : ∀ {ℓ} (sync : SynchronousConditions P ℓ) → IsPartiallyAsynchronouslySafe P (D₀ sync)
  sync⇒safe sync = record
    { m*         = {!!}
    ; m*-reached = {!!}
    }
{-
    shrinkSafety D₀⊆D[0] (ACO⇒partiallySafe (sync⇒ACO sync))
    where open UresinDubois3 P sync using (D₀⊆D[0])
-}


  {-
  -- Finite conditions implications

  finite⇒ACO : ∀ {ℓ} → FiniteConditions P ℓ → ACO P ℓ
  finite⇒ACO finite = aco
    where open UresinDubois4 P finite

  finite⇒safe : ∀ {ℓ} (fin : FiniteConditions P ℓ) → IsPartiallyAsynchronouslySafe P (FiniteConditions.D₀ fin)
  finite⇒safe finite = ACO⇒partiallySafe {!aco!}
    where open UresinDubois4 P finite



D₀ i x
!=<
Σ (ξ i ≼ᵢ x 
 ×
 (SynchronousConditions.poset finite M-poset.≼ᵢ x)
   (Parallelisation.syncIter P
     (StartingConditions.x₀
       (SynchronousConditions.start finite)
     )
     0 i
   )
 )
 (D₀ (SynchronousConditions.start finite) i)

    -}
