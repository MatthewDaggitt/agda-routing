open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤)
open import Data.Product using (∃; _,_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

open import RoutingLib.Relation.Unary.Indexed using (_∈_; U)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent as ACOImpliesConvergent
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Bisimulation as Bisimulation
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.DistanceImpliesACO as DistanceImpliesACO


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence where

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
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

module _ {a b ℓ₁ ℓ₂ n}
         {P∥ : AsyncIterable a ℓ₁ n}
         {Q∥ : AsyncIterable b ℓ₂ n}
         where

  bisimilar : Convergent P∥ → Bisimilar P∥ Q∥ → Convergent Q∥
  bisimilar = Bisimulation.bisimulation

------------------------------------------------------------------------
-- The operator being ACO implies that the iteration is convergent

module _ {a ℓ n} {P∥ : AsyncIterable a ℓ n} where

  ACO⇒convergent : ∀ {p} (aco : ACO P∥ p) → ConvergentOver P∥ (ACO.B₀ aco)
  ACO⇒convergent aco = ACOImpliesConvergent.convergent P∥ aco

------------------------------------------------------------------------
-- The operator fulfilling the ultrametric conditions implies the
-- iteration is convergent

module _ {a ℓ n} {P∥ : AsyncIterable a ℓ n} where

  ultra⇒ACO : UltrametricConditions P∥ → ACO P∥ ℓ
  ultra⇒ACO ultra = DistanceImpliesACO.aco ultra

  ultra⇒convergent : UltrametricConditions P∥ → Convergent P∥
  ultra⇒convergent ultra = convergentOver-universal
    (DistanceImpliesACO.B₀-univ ultra)
    (ACO⇒convergent (ultra⇒ACO ultra))
