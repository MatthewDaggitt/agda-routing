{-# OPTIONS --allow-unsolved-metas #-}

open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; ⊤; ⊥)
open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _∸_)
open import Data.Nat.Properties as ℕₚ using (n≤1+n; m∸n≤m; ≤-refl)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Product using (_×_; _,_)
open import Function using (const; id)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.Indexed.Homogeneous using (IRel; IsIndexedEquivalence; IsIndexedDecEquivalence)
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
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (RouteMapMatrix; IsComposition)
import RoutingLib.lmv34.Gamma_two.Properties as Gamma_two_Properties
import RoutingLib.lmv34.Omega_zero as Omega_zero
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)

module RoutingLib.lmv34.Omega_two
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open Routing algebra n renaming (_≈ₘ_ to infix 3 _≈ₘ_)
open RawRoutingAlgebra algebra using (≈-refl) renaming (S to 𝕊)
open Gamma_zero_Algebra algebra n using (_⊕ₘ_; _〔_〕; [_,_]_)
open Gamma_one isRoutingAlgebra A using (Γ₁)
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-sym; ≈ᵥ-trans; _⊕ᵥ_; ~_; ─_; _〚_〛; FinRoute-setoid; FinRoute-decSetoid)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong; ⊕-distributive; ⊕ᵥ-cong; Lemma-Γ₀=Γ₁; 〚〛-cong)
open Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂,ᵥ; Γ₂,ᵢ; Γ₂,ₒ)
open Gamma_two_Algebra isRoutingAlgebra n using ()
open Gamma_two_Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp using (Γ₂,ᵥ-cong; Γ₂,ᵢ-cong; Γ₂,ₒ-cong)
open Omega_zero algebra A using (Ω₀)
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_; refl to ≈ᵣ-refl)

-- Place these somewhere else. Generalise vector-indexed-equivalence
≈ᵥ,₂-isEquivalenceᵢ : IsIndexedEquivalence {I = Fin n} (const RoutingVector) _≈ᵥ_
≈ᵥ,₂-isEquivalenceᵢ = record
  { reflᵢ  = ≈ᵥ-refl
  ; symᵢ   = ≈ᵥ-sym
  ; transᵢ = ≈ᵥ-trans }

≈ᵥ,₂-isDecEquivalenceᵢ : IsIndexedDecEquivalence (const RoutingVector) _≈ᵥ_
≈ᵥ,₂-isDecEquivalenceᵢ = record
  { _≟ᵢ_           = {!!}
  ; isEquivalenceᵢ = ≈ᵥ,₂-isEquivalenceᵢ }

record Γ₂-Stateᵢ : Set a where
  constructor S₂,ᵢ
  field
    Vᵢ : RoutingSet
    Iᵢ : RoutingVector
    Oᵢ : RoutingVector

Γ₂ : (∀ i → Γ₂-Stateᵢ) → (∀ i → Γ₂-Stateᵢ)
Γ₂ S₂ i = S₂,ᵢ ((Γ₂,ᵥ (λ q → Γ₂-Stateᵢ.Iᵢ (S₂ q))) i)
               ((Γ₂,ᵢ (λ q → Γ₂-Stateᵢ.Oᵢ (S₂ q))) i)
               ((Γ₂,ₒ (λ q → Γ₂-Stateᵢ.Vᵢ (S₂ q))) i)


infix 3 _≈ₛ_
_≈ₛ_ : IRel {I = Fin n} (const Γ₂-Stateᵢ) (a ⊔ ℓ)
(S₂,ᵢ Vᵢ Iᵢ Oᵢ) ≈ₛ (S₂,ᵢ Vᵢ' Iᵢ' Oᵢ') =
         Vᵢ ↭ Vᵢ'  ×
         Iᵢ ≈ᵥ Iᵢ' ×
         Oᵢ ≈ᵥ Oᵢ'

Γ₂-cong : ∀ S S' → (∀ (i : Fin n) → S i ≈ₛ S' i) → (∀ i → Γ₂ S i ≈ₛ Γ₂ S' i)
Γ₂-cong S S' S=S' i =
  ( (Γ₂,ᵥ-cong λ q → {!!}) i
  , {!!}
  , {!!})

{-
Γ₂,ᵥ-cong : ∀ {I I'} → I ≈ᵥ,₂ I' → Γ₂,ᵥ I ≈ᵥ Γ₂,ᵥ I'
Γ₂,ᵥ-cong {I} {I'} I=I' = ⊕ᵥ-cong (↓-cong I=I') (≈ₘ⇒≈ᵥ ≈ₘ-refl)

Γ₂,ᵢ-cong : ∀ {O O'} → O ≈ᵥ,₂ O' → Γ₂,ᵢ O ≈ᵥ,₂ Γ₂,ᵢ O'
Γ₂,ᵢ-cong = 〖〗-cong

Γ₂,ₒ-cong : ∀ {V V'} → V ≈ᵥ V' → Γ₂,ₒ V ≈ᵥ,₂ Γ₂,ₒ V'
Γ₂,ₒ-cong = 【】-cong
-}

≈ₛ-isEquivalenceᵢ : IsIndexedEquivalence {I = Fin n} (const Γ₂-Stateᵢ) _≈ₛ_

≈ₛ-isDecEquivalenceᵢ : IsIndexedDecEquivalence (const Γ₂-Stateᵢ) _≈ₛ_
≈ₛ-isDecEquivalenceᵢ = record
  { _≟ᵢ_ = {!!}
  ; isEquivalenceᵢ = ≈ₛ-isEquivalenceᵢ }

Γ₂∥ : AsyncIterable a (a ⊔ ℓ) n
Γ₂∥ = record {
  Sᵢ   = const Γ₂-Stateᵢ;
  _≈ᵢ_ = _≈ₛ_;
  F    = Γ₂;
  isAsyncIterable = record {
    isDecEquivalenceᵢ = ≈ₛ-isDecEquivalenceᵢ;
    F-cong = {!Γ₂-cong!}
    }
  }

{-Ω₁ : Schedule n → RoutingVector → 𝕋 → RoutingVector
Ω₁ ψ = asyncIter Γ₁∥ ψ-}

-- Schedule reduction Ω₂ → Ω₁
r₂ : ∀ {n} → Schedule n → Schedule n
r₂ {n} ψ = record {α = α'; β = β'; β-causality = β'-causality }
  where open Schedule ψ
        α' : (t : 𝕋) → Subset n
        α' zero          = α zero
        α' (suc zero)    = ⊤
        α' (suc t)       = α t
        β' : (t : 𝕋) (i j : Fin n) → 𝕋
        β' zero i j       = β zero i j
        β' (suc zero) i j = zero
        β' (suc t) i j    = (β t i j) ∸ 1
        
        β'-causality : ∀ t i j → β' (suc t) i j ≤ t
        β'-causality zero i j    = z≤n
        β'-causality (suc t) i j = begin
          β' (suc (suc t)) i j ≡⟨⟩
          β (suc t) i j ∸ 1    ≤⟨ m∸n≤m (β (suc t) i j) 1 ⟩
          β (suc t) i j        ≤⟨ β-causality t i j ⟩
          t                    ≤⟨ n≤1+n t ⟩
          suc t ∎
          where open ℕₚ.≤-Reasoning

{-
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
-}
