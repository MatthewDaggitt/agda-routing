------------------------------------------------------------------------
-- This module publicly exports various pre-conditions for the
-- convergence of a dynamic asynchronous iteration as well as the
-- associated theorems.
------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static.Convergence where

open import Data.Fin.Subset using (Subset)
open import Data.Unit using (tt)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Unary using (Pred; U)

open import RoutingLib.Relation.Unary.Indexed using (IPred; Uᵢ; _∈ᵢ_)
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Static
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions
  as Conditions
import RoutingLib.Iteration.Asynchronous.Static.Convergence.ACOImpliesConverges
  as ACOImpliesConverges
import RoutingLib.Iteration.Asynchronous.Static.Convergence.AMCOImpliesACO
  as AMCOImpliesACO

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

  open AsyncIterable I∥
  
  AMCO⇒ACO : AMCO I∥ → ACO I∥ 0ℓ
  AMCO⇒ACO = AMCOImpliesACO.aco

  AMCO⇒converges : AMCO I∥ → Converges I∥
  AMCO⇒converges amco = begin⟨ amco ⟩
    ∴ AMCO       I∥    $⟨ AMCO⇒ACO ⟩
    ∴ ACO        I∥ 0ℓ $⟨ ACO⇒converges ⟩
    ∴ Converges  I∥    ∎
