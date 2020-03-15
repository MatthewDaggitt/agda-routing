{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (zero; suc)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Function using (const; id)
open import Level using (_⊔_)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.Indexed.Homogeneous using (IsIndexedEquivalence; IsIndexedDecEquivalence)
open import Relation.Nullary using (yes; no)

import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Omega_zero as Omega_zero
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

module RoutingLib.lmv34.Omega_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open Gamma_one isRoutingAlgebra A using (Γ₁)
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; _≈ᵥ_; ~_; FinRoute-setoid; FinRoute-decSetoid)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong)
open Omega_zero algebra A using (Ω₀)
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_)

≈ᵥ-isEquivalenceᵢ : IsIndexedEquivalence (const RoutingSet) _↭_
≈ᵥ-isEquivalenceᵢ = record
  { reflᵢ  = ↭-refl
  ; symᵢ   = ↭-sym
  ; transᵢ = ↭-trans }

≈ᵥ-isDecEquivalenceᵢ : IsIndexedDecEquivalence (const RoutingSet) _↭_
≈ᵥ-isDecEquivalenceᵢ = record
  { _≟ᵢ_           = _↭?_ _≟ᵣ_
  ; isEquivalenceᵢ = ≈ᵥ-isEquivalenceᵢ }

Γ₁∥ : AsyncIterable a (a ⊔ ℓ) n
Γ₁∥ = record {
  Sᵢ   = const RoutingSet;
  _≈ᵢ_ = _↭_;
  F    = Γ₁;
  isAsyncIterable = record {
    isDecEquivalenceᵢ = ≈ᵥ-isDecEquivalenceᵢ;
    F-cong = Γ₁-cong
    }
  }

Ω₁ : Schedule n → RoutingVector → 𝕋 → RoutingVector
Ω₁ ψ = asyncIter Γ₁∥ ψ

-- Reduction
r₁ : ∀ {n} → Schedule n → Schedule n
r₁ = id

-- Theorems
Ω₁=Ω₀ : ∀ ψ X t → (Ω₁ ψ (~ X) t) ≈ᵥ ~ (Ω₀ (r₁ ψ) X t)
Ω₁=Ω₀ ψ X zero i    = ↭-refl
Ω₁=Ω₀ ψ X (suc t) i with i ∈? α (suc t) where open Schedule ψ
... | no _  = begin
  {-asyncIter' Γ₁∥ ψ X (rec t ≤-refl) i-} {!!} ↭⟨ {!!} ⟩
  {-(~ (Ω₀ (r₁ ψ) X (suc t))) i-} {!!} ∎
  where open PermutationReasoning
... | yes _ = {!!}
