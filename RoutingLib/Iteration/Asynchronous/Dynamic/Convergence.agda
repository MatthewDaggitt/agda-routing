------------------------------------------------------------------------
-- Agda routing library
--
-- This module publicly exports various pre-conditions for the
-- convergence of a dynamic asynchronous iteration as well as the
-- associated theorems.
------------------------------------------------------------------------

open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Function.Base using (_∘_)
open import Level using (Level) renaming (zero to 0ℓ)
open import Relation.Unary using (Pred; _⊆_; Universal)

open import RoutingLib.Relation.Unary.Indexed using (IPred; Universalᵢ; _⊆ᵢ_)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Simulation as Simulation
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent as ACOImpliesConvergent
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO as AMCOImpliesACO

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence where

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    n : ℕ
    I∥ : AsyncIterable a ℓ₁ n
    J∥ : AsyncIterable b ℓ₂ n
    X₀ Y₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ
    Q R : Pred (Epoch × Subset n) ℓ
    
------------------------------------------------------------------------
-- Export convergence conditions publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-convergent : (I∥ : AsyncIterable a ℓ₁ 0) → Convergent I∥
|0|-convergent I∥ = record
  { localFP   = λ _ → record
    { x* = λ()
    ; k* = 0
    ; x*-fixed = λ()
    }
  ; reachesFP = λ _ _ _ _ _ ()
  }

------------------------------------------------------------------------
-- Changing the set of epochs/participants that convergence occurs over

shrinkConvergence : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂}
                    {Y₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₃} →
                    PartiallyConvergent I∥ X₀ Q →
                    Y₀ ⊆ᵢ X₀ → R ⊆ Q →
                    PartiallyConvergent I∥ Y₀ R
shrinkConvergence partial Y₀⊆X₀ R⊆Q = record
  { localFP   = localFP ∘ R⊆Q
  ; reachesFP = λ S x∈X₀ ep∈R → reachesFP S (Y₀⊆X₀ ∘ x∈X₀) (R⊆Q ep∈R)
  } where open PartiallyConvergent partial

completeConvergence : ∀ {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                      PartiallyConvergent I∥ X₀ Q →
                      Universalᵢ X₀ → Universal Q →
                      Convergent I∥
completeConvergence partial _∈X₀ _∈Q =
  shrinkConvergence partial (λ _ → _ ∈X₀) (λ _ → _ ∈Q)

------------------------------------------------------------------------
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

simulate-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                   {Y₀ : IPred (AsyncIterable.Sᵢ J∥) ℓ₂} →
                   PartiallySimulates I∥ J∥ X₀ Y₀ →
                   PartiallyConvergent I∥ X₀ Q →
                   PartiallyConvergent J∥ Y₀ Q
simulate-partial I∥⇉J∥ = Simulation.simulate I∥⇉J∥

simulate : I∥ Simulates J∥ → Convergent I∥ → Convergent J∥
simulate {I∥ = I∥} {J∥ = J∥} I∥⇉J∥ = simulate-partial I∥⇉J∥

------------------------------------------------------------------------
-- ACOs
--
-- The operator being ACO implies that the iteration is convergent

ACO⇒convergent-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                         PartialACO I∥ X₀ Q ℓ₃ →
                         PartiallyConvergent I∥ X₀ Q
ACO⇒convergent-partial = ACOImpliesConvergent.convergent _

ACO⇒convergent : ACO I∥ ℓ → Convergent I∥
ACO⇒convergent = ACO⇒convergent-partial

------------------------------------------------------------------------
-- AMCO
--
-- The operator being an AMCO implies that it is also an ACO
-- and hence that the iteration is convergent

AMCO⇒ACO-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                   PartialAMCO I∥ X₀ Q →
                   PartialACO I∥ X₀ Q _
AMCO⇒ACO-partial = AMCOImpliesACO.partialACO

AMCO⇒convergent-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                          PartialAMCO I∥ X₀ Q →
                          PartiallyConvergent I∥ X₀ Q
AMCO⇒convergent-partial = ACO⇒convergent-partial ∘ AMCO⇒ACO-partial

AMCO⇒ACO : AMCO I∥ → ACO I∥ _
AMCO⇒ACO = AMCO⇒ACO-partial

AMCO⇒convergent : AMCO I∥ → Convergent I∥
AMCO⇒convergent = AMCO⇒convergent-partial
