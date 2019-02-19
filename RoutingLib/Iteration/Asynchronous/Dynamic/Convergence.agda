------------------------------------------------------------------------
-- This module publicly exports various pre-conditions for the
-- convergence of a dynamic asynchronous iteration as well as the
-- associated theorems.
------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence where

open import Data.Fin.Subset using (Subset)
open import Data.Unit using (tt)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Unary using (Pred; U)

open import RoutingLib.Relation.Unary.Indexed using (IPred; Uᵢ; _∈ᵢ_)
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Simulation as Simulation
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent as ACOImpliesConvergent
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO as AMCOImpliesACO

------------------------------------------------------------------------
-- Export convergence conditions publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-convergent : ∀ {a ℓ} (I∥ : AsyncIterable a ℓ 0) → Convergent I∥
|0|-convergent I∥ = record
  { k*         = λ _ _ → 0
  ; x*         = λ _ _ ()
  ; x*-fixed   = λ _ _ ()
  ; x*-reached = λ _ _ _ _ ()
  }

------------------------------------------------------------------------
-- If a convergent iteration is bisimilar to a second iteration then
-- that iteration is also convergent

module _ {a b ℓ₁ ℓ₂ n}
         {I∥ : AsyncIterable a ℓ₁ n}
         {J∥ : AsyncIterable b ℓ₂ n}
         where

  simulate-partial : ∀ {ℓ₃ ℓ₄ ℓ₅} {Q : Pred (Subset n) ℓ₃}
                      {X₀ : IPred (AsyncIterable.Sᵢ I∥) ℓ₄}
                      {Y₀ : IPred (AsyncIterable.Sᵢ J∥) ℓ₅} →
                      (I∥⇉J∥ : Simulates I∥ J∥) →
                      (∀ {x} → x ∈ᵢ Y₀ → Simulates.from I∥⇉J∥ x ∈ᵢ X₀) →
                      PartiallyConvergent I∥ X₀ Q →
                      PartiallyConvergent J∥ Y₀ Q
  simulate-partial I∥⇉J∥ Y₀⊆X₀ = Simulation.simulate I∥⇉J∥ Y₀⊆X₀

  simulate : Simulates I∥ J∥ → Convergent I∥ → Convergent J∥
  simulate I∥⇉J∥ = begin⟨_⟩
    ∴ Convergent I∥               $⟨ convergent⇒partiallyConvergent ⟩
    ∴ PartiallyConvergent I∥ Uᵢ U $⟨ simulate-partial I∥⇉J∥ (λ _ _ → tt) ⟩
    ∴ PartiallyConvergent J∥ Uᵢ U $⟨ partiallyConvergent⇒convergent′ ⟩
    ∴ Convergent J∥               ∎

------------------------------------------------------------------------
-- ACOs
--
-- The operator being ACO implies that the iteration is convergent

module _ {a ℓ n} {I∥ : AsyncIterable a ℓ n} where

  open AsyncIterable I∥

  ACO⇒convergent-partial : ∀ {ℓ₁ ℓ₂ ℓ₃} →
                           {X₀ : IPred Sᵢ ℓ₁} →
                           {Q : Pred (Subset n) ℓ₂} →
                           PartialACO I∥ X₀ Q ℓ₃ →
                           PartiallyConvergent I∥ X₀ Q
  ACO⇒convergent-partial = ACOImpliesConvergent.convergent I∥

  ACO⇒convergent : ∀ {ℓ} → ACO I∥ ℓ → Convergent I∥
  ACO⇒convergent {ℓ} = begin⟨_⟩
    ∴ ACO                 I∥ ℓ       $⟨ ACO⇒partialACO I∥ ⟩
    ∴ PartialACO          I∥ Uᵢ U ℓ  $⟨ ACO⇒convergent-partial ⟩
    ∴ PartiallyConvergent I∥ Uᵢ U    $⟨ partiallyConvergent⇒convergent′ ⟩
    ∴ Convergent          I∥        ∎

------------------------------------------------------------------------
-- AMCO
--
-- The operator being an AMCO implies that it is also an ACO
-- and hence that the iteration is convergent

module _ {a ℓ n} {I∥ : AsyncIterable a ℓ n} where

  open AsyncIterable I∥

  AMCO⇒ACO-partial : ∀ {ℓ₂} {Q : Pred (Subset n) ℓ₂} →
                     PartialAMCO I∥ Q → PartialACO  I∥ Uᵢ Q ℓ
  AMCO⇒ACO-partial = AMCOImpliesACO.aco

  AMCO⇒ACO : AMCO I∥ → ACO I∥ ℓ
  AMCO⇒ACO = begin⟨_⟩
    ∴ AMCO        I∥        $⟨ AMCO⇒partialAMCO I∥ ⟩
    ∴ PartialAMCO I∥ U      $⟨ AMCO⇒ACO-partial ⟩
    ∴ PartialACO  I∥ Uᵢ U ℓ  $⟨ partialACO⇒ACO′ I∥ ⟩
    ∴ ACO         I∥ ℓ      ∎

  AMCO⇒convergent-partial : ∀ {ℓ₂} {Q : Pred (Subset n) ℓ₂} →
                            PartialAMCO I∥ Q → PartiallyConvergent I∥ Uᵢ Q
  AMCO⇒convergent-partial {Q = Q} = begin⟨_⟩
    ∴ PartialAMCO         I∥ Q      $⟨ AMCO⇒ACO-partial ⟩
    ∴ PartialACO          I∥ Uᵢ Q ℓ  $⟨ ACO⇒convergent-partial ⟩
    ∴ PartiallyConvergent I∥ Uᵢ Q    ∎

  AMCO⇒convergent : AMCO I∥ → Convergent I∥
  AMCO⇒convergent amco = begin⟨ amco ⟩
    ∴ AMCO       I∥   $⟨ AMCO⇒ACO ⟩
    ∴ ACO        I∥ ℓ $⟨ ACO⇒convergent ⟩
    ∴ Convergent I∥   ∎
