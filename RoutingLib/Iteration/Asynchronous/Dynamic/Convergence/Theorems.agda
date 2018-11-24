open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤)
open import Data.Product using (∃; _,_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

open import RoutingLib.Relation.Unary.Indexed using (_∈_; U)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.ACOToSafe as ACOToSafe
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.Bisimulation as Bisimulation
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.UltrametricToACO as UltrametricToACO


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Theorems where

------------------------------------------------------------------------
-- Export convergence conditions publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-convergent : ∀ {a ℓ} (P∥ : AsyncIterable a ℓ 0) → Convergent P∥
|0|-convergent P∥ = record
  { x*         = λ _ _ ()
  ; x*-fixed   = λ _ _ ()
  ; x*-reached = λ _ _ → 0 , λ _ _ ()
  }

------------------------------------------------------------------------
-- The operator being ACO implies that the iteration is convergent

module _ {a ℓ n} {P∥ : AsyncIterable a ℓ n} where

  ACO⇒convergent : ∀ {p} (aco : ACO P∥ p) → ConvergentOver P∥ (ACO.B₀ aco)
  ACO⇒convergent aco = ACOToSafe.isSafe P∥ aco

------------------------------------------------------------------------
-- The operator fulfilling the ultrametric conditions implies the
-- iteration is convergent

module _ {a ℓ n} {P∥ : AsyncIterable a ℓ n} where

  ultra⇒ACO : UltrametricConditions P∥ → ACO P∥ ℓ
  ultra⇒ACO ultra = UltrametricToACO.aco ultra

  ultra⇒convergent : UltrametricConditions P∥ → Convergent P∥
  ultra⇒convergent ultra = convergentOver-universal
    (UltrametricToACO.B₀-univ ultra)
    (ACO⇒convergent (ultra⇒ACO ultra))

------------------------------------------------------------------------
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

module _ {a₁ a₂ ℓ₁ ℓ₂ n}
         {P∥ : AsyncIterable a₁ ℓ₁ n}
         {Q∥ : AsyncIterable a₂ ℓ₂ n}
         where

  bisimilar : Convergent P∥ → Bisimilar P∥ Q∥ → Convergent Q∥
  bisimilar = Bisimulation.bisimulation
