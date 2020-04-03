--------------------------------------------------------------------------------
-- This module constructs the static schedule that corresponds to the fully
-- synchronous computation
--------------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ; zero; suc; _∸_)

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
  {n : ℕ} where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤)
open import Data.Fin.Subset.Properties using (_∈?_; ∈⊤)
open import Data.Nat using (z≤n; s≤s; _≤_; _<_; _+_)
open import Data.Nat.Properties
open import Function using (const)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Indexed.Homogeneous.Bundles
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Schedule
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod
  as Pseudoperiod
open import RoutingLib.Iteration.Synchronous using (_^_)

--------------------------------------------------------------------------------
-- Definition

αˢʸⁿᶜ : 𝕋 → Subset n
αˢʸⁿᶜ = const ⊤

βˢʸⁿᶜ : 𝕋 → Fin n → Fin n → 𝕋
βˢʸⁿᶜ t _ _ = t ∸ 1

βˢʸⁿᶜ-causality : ∀ t i j → βˢʸⁿᶜ(suc t) i j ≤ t
βˢʸⁿᶜ-causality _ _ _ = ≤-refl

ψˢʸⁿᶜ : Schedule n
ψˢʸⁿᶜ = record
  { α           = αˢʸⁿᶜ
  ; β           = βˢʸⁿᶜ
  ; β-causality = βˢʸⁿᶜ-causality
  }

--------------------------------------------------------------------------------
-- Properties

open Pseudoperiod ψˢʸⁿᶜ

βˢʸⁿᶜ-expiry : ∀ {t₁ t₂} i j → t₁ < t₂ → t₁ ≤ βˢʸⁿᶜ t₂ i j
βˢʸⁿᶜ-expiry i j (s≤s t₁≤t₂) = t₁≤t₂

ψˢʸⁿᶜ-activeIn : ∀ t i → i IsActiveIn [ t , suc t ]
ψˢʸⁿᶜ-activeIn t i = mkₐ (suc t) ≤-refl ≤-refl ∈⊤

ψˢʸⁿᶜ-expiresIn : ∀ t i → MessagesTo i ExpireIn [ t , t ]
ψˢʸⁿᶜ-expiresIn t i = mkₑ ≤-refl (λ t<s j → βˢʸⁿᶜ-expiry i j t<s)

ψˢʸⁿᶜ-pseudocycle : ∀ t → Pseudocycle [ t , suc t ]
ψˢʸⁿᶜ-pseudocycle t = record
  { m          = const t
  ; start≤end  = n≤1+n t
  ; start≤midᵢ = const ≤-refl
  ; midᵢ≤end   = const (n≤1+n t)
  ; β[s,m]     = ψˢʸⁿᶜ-expiresIn t
  ; α[m,e]     = ψˢʸⁿᶜ-activeIn t
  }

ψˢʸⁿᶜ-multiPseudocycle : ∀ t k → MultiPseudocycle k [ t , t + k ]
ψˢʸⁿᶜ-multiPseudocycle t zero    rewrite +-identityʳ t = none
ψˢʸⁿᶜ-multiPseudocycle t (suc k) rewrite +-suc t k     =
  next (suc t) (ψˢʸⁿᶜ-pseudocycle t) (ψˢʸⁿᶜ-multiPseudocycle (suc t) k)

-- TODO: Show that the synchronous schedule is indeed turns an asynchronous
-- iteration into its underlying synchronous function.
module _ {a ℓ} (I∥ : AsyncIterable a ℓ n) where
  open AsyncIterable I∥

  ψˢʸⁿᶜ-isSynchronous : ∀ x₀ t → asyncIter I∥ ψˢʸⁿᶜ x₀ t ≈ (F ^ t) x₀
  ψˢʸⁿᶜ-isSynchronous x₀ zero    i = ≈ᵢ-refl
  ψˢʸⁿᶜ-isSynchronous x₀ (suc t) i with i ∈? αˢʸⁿᶜ (suc t)
  ... | no i∉α  = contradiction ∈⊤ i∉α
  ... | yes i∈α = {!!}
    where ≈ᵢ-Setoidᵢ : Setoid a ℓ
          ≈ᵢ-Setoidᵢ = record
                { Carrier = Sᵢ i
                ; _≈_ = _≈ᵢ_ {i}
                ; isEquivalence = record
                { refl  = ≈ᵢ-refl {i}
                ; sym   = ≈ᵢ-sym {i}
                ; trans = ≈ᵢ-trans {i}
                }
                } 
          open EqReasoning ≈ᵢ-Setoidᵢ
          prf : asyncIter I∥ ψˢʸⁿᶜ x₀ (suc t) i ≈ᵢ (F ^ (suc t)) x₀ i
          prf = begin
                {!asyncIter I∥ ψˢʸⁿᶜ x₀ (suc t) i!} ≈⟨ {!!} ⟩
                {!!} ≈⟨ {!!} ⟩
                {!(F ((F ^ t) x₀)) i!} ≈⟨ {!!} ⟩
                {!(F ^ suc t) x₀ i!} ∎
