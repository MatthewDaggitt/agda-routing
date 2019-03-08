------------------------------------------------------------------------
-- This module publicly exports various pre-conditions for the
-- convergence of a dynamic asynchronous iteration as well as the
-- associated theorems.
------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static.Convergence where

open import Data.Fin.Subset using (Subset)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Level using (0ℓ)

open import RoutingLib.Relation.Unary.Indexed using (IPred; Uᵢ; _∈ᵢ_)
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Static
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions
  as Conditions
import RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConverges
  as ACOImpliesConverges
import RoutingLib.Iteration.Asynchronous.Static.Convergence.AMCOImpliesACO
  as AMCOImpliesACO
import RoutingLib.Iteration.Asynchronous.Static.Convergence.SyncImpliesACO
  as SyncImpliesACO

------------------------------------------------------------------------
-- Export convergence conditions publically

open Conditions public

------------------------------------------------------------------------
-- The empty computation is always convergent

|0|-converges : ∀ {a ℓ} (I∥ : AsyncIterable a ℓ 0) → Converges I∥
|0|-converges I∥ = record
  { k*         = 0
  ; x*         = λ ()
  ; x*-fixed   = λ ()
  ; x*-reached = λ _ _ _ _ ()
  }

------------------------------------------------------------------------
-- ACO

module _ {a ℓ n} {I∥ : AsyncIterable a ℓ n} where

  open AsyncIterable I∥

  ACO⇒converges-partial : ∀ {ℓ₁ ℓ₂} →
                          {X₀ : IPred Sᵢ ℓ₁} →
                          PartialACO I∥ X₀ ℓ₂ →
                          PartiallyConverges I∥ X₀
  ACO⇒converges-partial = ACOImpliesConverges.convergent I∥

  ACO⇒converges : ∀ {ℓ} → ACO I∥ ℓ → Converges I∥
  ACO⇒converges {ℓ} = begin⟨_⟩
    ∴ ACO                I∥ ℓ    $⟨ ACO⇒partialACO I∥ ⟩
    ∴ PartialACO         I∥ Uᵢ ℓ $⟨ ACO⇒converges-partial ⟩
    ∴ PartiallyConverges I∥ Uᵢ   $⟨ partiallyConverges⇒converges′ I∥ ⟩
    ∴ Converges          I∥      ∎

------------------------------------------------------------------------
-- AMCO

module _ {a ℓ n} {I∥ : AsyncIterable a ℓ n} where

  AMCO⇒ACO-partial : ∀ {p} {X₀ : IPred _ p} → PartialAMCO I∥ X₀ → PartialACO I∥ X₀ p
  AMCO⇒ACO-partial = AMCOImpliesACO.aco

  AMCO⇒converges-partial : ∀ {p} {X₀ : IPred _ p} → PartialAMCO I∥ X₀ → PartiallyConverges I∥ X₀
  AMCO⇒converges-partial amco = ACO⇒converges-partial (AMCO⇒ACO-partial amco)
  
  AMCO⇒ACO : AMCO I∥ → ACO I∥ 0ℓ
  AMCO⇒ACO = begin⟨_⟩
    ∴ AMCO        I∥       $⟨ AMCO⇒partialAMCO I∥ ⟩
    ∴ PartialAMCO I∥ Uᵢ    $⟨ AMCO⇒ACO-partial ⟩
    ∴ PartialACO  I∥ Uᵢ 0ℓ $⟨ partialACO⇒ACO′ I∥ ⟩
    ∴ ACO         I∥ 0ℓ    ∎
  
  AMCO⇒converges : AMCO I∥ → Converges I∥
  AMCO⇒converges amco = ACO⇒converges (AMCO⇒ACO amco)

------------------------------------------------------------------------
-- Synchronous conditions

module _ {a ℓ n} {I∥ : AsyncIterable a ℓ n} where

  open AsyncIterable I∥
  
  sync⇒converges-partial : ∀ {b c} {X₀ : IPred Sᵢ b} →
                           PartialSynchronousConditions I∥ X₀ c →
                           PartiallyConverges I∥ X₀
  sync⇒converges-partial sync = record
    { x*         = Sync.x*
    ; k*         = Sync.k*
    ; x*-fixed   = Sync.x*-fixed
    ; x*-reached = λ x∈X₀ → PartiallyConverges.x*-reached (ACO⇒converges-partial (SyncProofs.aco x∈X₀)) (SyncProofs.y∈B₀ x∈X₀)
    } where
    module Sync       = PartialSynchronousConditions sync
    module SyncProofs = SyncImpliesACO I∥ sync
  
  sync⇒converges : ∀ {ℓ} → SynchronousConditions I∥ ℓ → Converges I∥
  sync⇒converges {ℓ} = begin⟨_⟩
    ∴ SynchronousConditions         I∥ ℓ    $⟨ sync⇒partialSync I∥ ⟩
    ∴ PartialSynchronousConditions  I∥ Uᵢ ℓ $⟨ sync⇒converges-partial ⟩
    ∴ PartiallyConverges            I∥ Uᵢ   $⟨ partiallyConverges⇒converges′ I∥ ⟩
    ∴ Converges                     I∥      ∎
