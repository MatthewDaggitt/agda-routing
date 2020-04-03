{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; ⊤; ⊥)
open import Data.List using (tabulate)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _∸_)
open import Data.Nat.Properties as ℕₚ using (n≤1+n; m∸n≤m; ≤-refl)
open import Data.Product using (_,_)
open import Function using (const; id)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.Indexed.Homogeneous using (IsIndexedEquivalence; IsIndexedDecEquivalence)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)

import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra
import RoutingLib.lmv34.Gamma_zero.Properties as Gamma_zero_Properties
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_one.Properties as Gamma_one_Properties
import RoutingLib.lmv34.Omega_zero as Omega_zero
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

module RoutingLib.lmv34.Omega_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n renaming (_≈ₘ_ to infix 3 _≈ₘ_)
open RawRoutingAlgebra algebra using (≈-refl) renaming (S to 𝕊)
open Gamma_zero_Algebra algebra n using (_⊕ₘ_; _〔_〕; [_,_]_)
open Gamma_one isRoutingAlgebra A using (Γ₁)
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-sym; _⊕ᵥ_; _†; ~_; ─_; lookup-d; _〚_〛; FinRoute-setoid; FinRoute-decSetoid)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong; ⊕-distributive; ⊕ᵥ-cong; Lemma-Γ₀=Γ₁; 〚〛-cong)
open Omega_zero algebra A using (Ω₀)
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_; refl to ≈ᵣ-refl)

-- Place these somewhere else. Generalise vector-indexed-equivalence
≈ᵥ-isEquivalenceᵢ : IsIndexedEquivalence {I = Fin n} (const RoutingSet) _↭_
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

-- Schedule reduction Ω₁ → Ω₀
r₁ : ∀ {n} → Schedule n → Schedule n
r₁ = id

-- Lemmas
-- Maybe try to merely have a unique destination postulate for RoutingVectors
postulate
  ─-~-inverse : ∀ V → ~(─ V) ≈ᵥ V
  ─-cong : ∀ {U V} → U ≈ᵥ V → ─ U ≈ₘ ─ V -- requires uniqueness of destination

~-─-inverse : ∀ X → ─(~ X) ≈ₘ X
~-─-inverse X i j = begin
  (─(~ X)) i j ≡⟨⟩
  lookup-d ((~ X) i) j ≡⟨⟩
  lookup-d ((tabulate (λ d → d , X i d)) †) j ≈⟨ {!!} ⟩
  X i j        ∎
  where open EqReasoning 𝕊

─-⊕-distributive : ∀ U V → ─ (U ⊕ᵥ V) ≈ₘ (─ U) ⊕ₘ (─ V)
─-⊕-distributive U V = begin
  ─ (U ⊕ᵥ V)               ≈⟨ ─-cong (⊕ᵥ-cong (≈ᵥ-sym (─-~-inverse U)) (≈ᵥ-sym (─-~-inverse V))) ⟩
  ─ ((~(─ U)) ⊕ᵥ (~(─ V))) ≈⟨ ─-cong (≈ᵥ-sym (⊕-distributive (─ U) (─ V))) ⟩
  ─ (~ ((─ U) ⊕ₘ (─ V)))   ≈⟨ ~-─-inverse ((─ U) ⊕ₘ (─ V)) ⟩
  (─ U) ⊕ₘ (─ V) ∎
  where open EqReasoning ℝ𝕄ₛ

─-〚_〛-distributive : ∀ A V → ─ (A 〚 V 〛) ≈ₘ A 〔 (─ V) 〕
─-〚_〛-distributive A V = begin
  ─ (A 〚 V 〛)       ≈⟨ ─-cong (〚〛-cong (≈ᵥ-sym (─-~-inverse V))) ⟩
  ─ (A 〚 ~(─ V) 〛)  ≈⟨ ─-cong Lemma-Γ₀=Γ₁ ⟩
  ─ (~ (A 〔(─ V)〕)) ≈⟨ ~-─-inverse (A 〔(─ V)〕) ⟩
  A 〔(─ V)〕 ∎
  where open EqReasoning ℝ𝕄ₛ

─-[_,_]-distributive : ∀ U V S → ─([ U , V ] S) ≈ₘ [ (─ U) , (─ V) ] S
─-[_,_]-distributive U V S i j with i ∈? S
... | yes _ = ≈-refl
... | no _  = ≈-refl

-- Move to Omega_2
⊕-[_,_]-distributive : ∀ U V W S → ([ U , V ] S) ⊕ᵥ W ≈ᵥ [ U ⊕ᵥ W , V ⊕ᵥ W ] S
⊕-[_,_]-distributive U V W S i with i ∈? S
... | yes _ = ↭-refl
... | no _  = ↭-refl

-- Theorems
-- Figure out a way to reason with the decreasing argument
Ω₁=Ω₀ : ∀ ψ V t → ─ (Ω₁ ψ V t) ≈ₘ Ω₀ (r₁ ψ) (─ V) t
Ω₁=Ω₀ ψ V zero    = ≈ₘ-refl
Ω₁=Ω₀ ψ V (suc t) = begin
  ─ (Ω₁ ψ V (suc t))        ≈⟨ {!!} ⟩
  ─ ([ {!!} , Ω₁ ψ V t ] α (suc t)) ≈⟨ {!!} ⟩
  Ω₀ (r₁ ψ) (─ V) (suc t)  ∎
  where open EqReasoning ℝ𝕄ₛ
        open Schedule ψ
