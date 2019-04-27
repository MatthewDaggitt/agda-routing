------------------------------------------------------------------------
-- Agda routing library
--
-- This module publicly exports various pre-conditions for the
-- convergence of a dynamic asynchronous iteration as well as the
-- associated theorems.
------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence where

open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Level using (Level) renaming (zero to 0ℓ)
open import Relation.Unary using (Pred; U)

open import RoutingLib.Relation.Unary.Indexed using (IPred; Uᵢ; _∈ᵢ_)
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Simulation as Simulation
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent as ACOImpliesConvergent
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO as AMCOImpliesACO

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    n : ℕ
    I∥ : AsyncIterable a ℓ₁ n
    J∥ : AsyncIterable b ℓ₂ n

------------------------------------------------------------------------
-- Export convergence conditions publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-convergent : (I∥ : AsyncIterable a ℓ₁ 0) → Convergent I∥
|0|-convergent I∥ = record
  { k*         = λ _ _ → 0
  ; x*         = λ _ _ ()
  ; x*-fixed   = λ _ _ ()
  ; x*-reached = λ _ _ _ _ ()
  }

------------------------------------------------------------------------
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

simulate-partial : ∀ {ℓ₃ ℓ₄ ℓ₅} {Q : Pred (Subset n) ℓ₃}
                    {X₀ : IPred _ ℓ₄}
                    {Y₀ : IPred _ ℓ₅} →
                    (I∥⇉J∥ : I∥ Simulates J∥) →
                    (∀ {x} → x ∈ᵢ Y₀ → _Simulates_.from I∥⇉J∥ x ∈ᵢ X₀) →
                    PartiallyConvergent I∥ X₀ Q →
                    PartiallyConvergent J∥ Y₀ Q
simulate-partial I∥⇉J∥ Y₀⊆X₀ = Simulation.simulate I∥⇉J∥ Y₀⊆X₀

simulate : I∥ Simulates J∥ → Convergent I∥ → Convergent J∥
simulate {I∥ = I∥} {J∥ = J∥} I∥⇉J∥ = begin⟨_⟩
  ∴ Convergent I∥               $⟨ convergent⇒partiallyConvergent ⟩
  ∴ PartiallyConvergent I∥ Uᵢ U $⟨ simulate-partial I∥⇉J∥ (λ _ _ → tt) ⟩
  ∴ PartiallyConvergent J∥ Uᵢ U $⟨ partiallyConvergent⇒convergent′ ⟩
  ∴ Convergent J∥               ∎

------------------------------------------------------------------------
-- ACOs
--
-- The operator being ACO implies that the iteration is convergent

ACO⇒convergent-partial : ∀ {ℓ₁ ℓ₂ ℓ₃} →
                         {X₀ : IPred _ ℓ₁} →
                         {Q : Pred (Subset n) ℓ₂} →
                         PartialACO I∥ X₀ Q ℓ₃ →
                         PartiallyConvergent I∥ X₀ Q
ACO⇒convergent-partial {I∥ = I∥} = ACOImpliesConvergent.convergent I∥

ACO⇒convergent : ACO I∥ ℓ → Convergent I∥
ACO⇒convergent {I∥ = I∥} = begin⟨_⟩
  ∴ ACO                 I∥ _       $⟨ ACO⇒partialACO I∥ ⟩
  ∴ PartialACO          I∥ Uᵢ U _  $⟨ ACO⇒convergent-partial ⟩
  ∴ PartiallyConvergent I∥ Uᵢ U    $⟨ partiallyConvergent⇒convergent′ ⟩
  ∴ Convergent          I∥         ∎

------------------------------------------------------------------------
-- AMCO
--
-- The operator being an AMCO implies that it is also an ACO
-- and hence that the iteration is convergent

AMCO⇒ACO-partial : ∀ {ℓ₂} {Q : Pred (Subset n) ℓ₂} →
                   PartialAMCO I∥ Q → PartialACO I∥ Uᵢ Q _
AMCO⇒ACO-partial = AMCOImpliesACO.aco

AMCO⇒ACO : AMCO I∥ → ACO I∥ _
AMCO⇒ACO {I∥ = I∥} = begin⟨_⟩
  ∴ AMCO        I∥        $⟨ AMCO⇒partialAMCO I∥ ⟩
  ∴ PartialAMCO I∥ U      $⟨ AMCO⇒ACO-partial ⟩
  ∴ PartialACO  I∥ Uᵢ U _  $⟨ partialACO⇒ACO′ I∥ ⟩
  ∴ ACO         I∥ _      ∎

AMCO⇒convergent-partial : ∀ {ℓ₂} {Q : Pred (Subset n) ℓ₂} →
                          PartialAMCO I∥ Q → PartiallyConvergent I∥ Uᵢ Q
AMCO⇒convergent-partial {I∥ = I∥} {Q = Q} = begin⟨_⟩
  ∴ PartialAMCO         I∥ Q      $⟨ AMCO⇒ACO-partial ⟩
  ∴ PartialACO          I∥ Uᵢ Q _  $⟨ ACO⇒convergent-partial ⟩
  ∴ PartiallyConvergent I∥ Uᵢ Q    ∎

AMCO⇒convergent : AMCO I∥ → Convergent I∥
AMCO⇒convergent {I∥ = I∥} amco = begin⟨ amco ⟩
  ∴ AMCO       I∥   $⟨ AMCO⇒ACO ⟩
  ∴ ACO        I∥ _ $⟨ ACO⇒convergent ⟩
  ∴ Convergent I∥   ∎
