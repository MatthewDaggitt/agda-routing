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
    C D : Pred (Epoch × Subset n) ℓ
    
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
                    PartiallyConvergent I∥ X₀ C →
                    Y₀ ⊆ᵢ X₀ → D ⊆ C →
                    PartiallyConvergent I∥ Y₀ D
shrinkConvergence partial Y₀⊆X₀ D⊆C = record
  { localFP   = λ ep∈C → localFP (D⊆C ep∈C)
  ; reachesFP = λ S x∈X₀ ep∈R → reachesFP S (Y₀⊆X₀ ∘ x∈X₀) (D⊆C ep∈R)
  } where open PartiallyConvergent partial

completeConvergence : ∀ {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                      PartiallyConvergent I∥ X₀ C →
                      Universalᵢ X₀ → Universal C →
                      Convergent I∥
completeConvergence partial _∈X₀ _∈C =
  shrinkConvergence partial (λ _ → _ ∈X₀) (λ _ → _ ∈C)

------------------------------------------------------------------------
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

simulate-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                   {Y₀ : IPred (AsyncIterable.Sᵢ J∥) ℓ₂} →
                   PartiallySimulates I∥ J∥ X₀ Y₀ →
                   PartiallyConvergent I∥ X₀ C →
                   PartiallyConvergent J∥ Y₀ C
simulate-partial I∥⇉J∥ = Simulation.simulate I∥⇉J∥

simulate : I∥ Simulates J∥ → Convergent I∥ → Convergent J∥
simulate {I∥ = I∥} {J∥ = J∥} I∥⇉J∥ = simulate-partial I∥⇉J∥

------------------------------------------------------------------------
-- ACOs
--
-- The operator being ACO implies that the iteration is convergent

ACO⇒convergent-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                         IsValidInitialSet I∥ X₀ → 
                         PartialACO I∥ X₀ C ℓ₃ →
                         PartiallyConvergent I∥ X₀ C
ACO⇒convergent-partial v p = ACOImpliesConvergent.convergent _ v p

ACO⇒convergent : ACO I∥ ℓ → Convergent I∥
ACO⇒convergent = ACO⇒convergent-partial (Uᵢ-validInitialSet _)

------------------------------------------------------------------------
-- AMCO
--
-- The operator being an AMCO implies that it is also an ACO
-- and hence that the iteration is convergent

AMCO⇒ACO-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                   IsValidInitialSet I∥ X₀ → 
                   PartialAMCO I∥ X₀ C →
                   PartialACO I∥ X₀ C _
AMCO⇒ACO-partial X-valid AMCO ep∈C = AMCOImpliesACO.localACO X-valid (AMCO ep∈C)

AMCO⇒convergent-partial : {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₂} →
                          IsValidInitialSet I∥ X₀ → 
                          PartialAMCO I∥ X₀ C →
                          PartiallyConvergent I∥ X₀ C
AMCO⇒convergent-partial v p = ACO⇒convergent-partial v (AMCO⇒ACO-partial v p)

AMCO⇒ACO : AMCO I∥ → ACO I∥ _
AMCO⇒ACO = AMCO⇒ACO-partial (Uᵢ-validInitialSet _)

AMCO⇒convergent : AMCO I∥ → Convergent I∥
AMCO⇒convergent = AMCO⇒convergent-partial (Uᵢ-validInitialSet _)
