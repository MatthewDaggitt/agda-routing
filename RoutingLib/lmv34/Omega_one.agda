open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Fin.Subset using (Subset; ⊤; ⊥)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List using (tabulate)
import Data.List.Relation.Binary.Permutation.Setoid as PermutationEq
open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _<_; _∸_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties as ℕₚ using (n≤1+n; m∸n≤m; ≤-refl)
open import Data.Product using (_,_)
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties using () renaming (decSetoid to decSetoidᵥ)
open import Function using (const; id)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.Indexed.Homogeneous using (IsIndexedEquivalence; IsIndexedDecEquivalence; IndexedDecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)

import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')
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
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; ψˢʸⁿᶜ-isSynchronous)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous

module RoutingLib.lmv34.Omega_one
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open Routing algebra n renaming (_≈ₘ_ to infix 3 _≈ₘ_)
open RawRoutingAlgebra algebra using (_▷_; ≈-refl) renaming (S to 𝕊)
open Gamma_zero algebra A using (Γ₀)
open Gamma_zero_Algebra algebra n using (_⊕ₘ_; _〔_〕)
open Gamma_zero_Properties algebra A using (Γ₀-cong; ⊕ₘ-cong)
open Gamma_one isRoutingAlgebra A using (Γ₁)
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingSet; RoutingVector; _≈ᵥ_; ≈ᵥ-refl; ≈ᵥ-sym; ⨁ₛ; _⊕ᵥ_; _†; ~_; ─_; lookup-d; _[_]; _〚_〛; FinRoute-setoid; FinRoute-decSetoid)
open Gamma_one_Properties isRoutingAlgebra A using (Γ₁-cong; ⊕-distributive; ⨁ₛ-cong; []-cong; ⊕ᵥ-cong; Lemma-Γ₀=Γ₁; 〚〛-cong)
open Omega_zero algebra A using (Ω₀'; Ω₀; [_,_]_)
open PermutationEq FinRoute-setoid
open PermutationProperties FinRoute-setoid using (_↭?_; ↭-decSetoid)
open DecSetoid FinRoute-decSetoid using () renaming (_≟_ to _≟ᵣ_; refl to ≈ᵣ-refl)

≈ᵥ-decSetoidᵢ : IndexedDecSetoid _ _ _
≈ᵥ-decSetoidᵢ = triviallyIndexDecSetoid (Fin n) (↭-decSetoid _≟ᵣ_)

-- Generalised (asynchronous) matrix multiplication
_⟦_⟧' : AdjacencyMatrix → (Fin n → Fin n → RoutingSet) → RoutingVector
(A ⟦ f ⟧') i = ⨁ₛ (λ q → (A i q ▷_) [ f i q ])

⟦_⟧-cong' : ∀ {A} {V V'} → (∀ i → V i ≈ᵥ V' i) → A ⟦ V ⟧' ≈ᵥ A ⟦ V' ⟧'
⟦_⟧-cong' V=V' i = ⨁ₛ-cong (λ {q} → []-cong (V=V' i q))

-- Generalised (asynchronous) operator
Γ₁' : (Fin n → Fin n → RoutingSet) → RoutingVector
Γ₁' f = A ⟦ f ⟧' ⊕ᵥ ~ I

Γ₁-cong' : ∀ {V V'} → (∀ i → V i ≈ᵥ V' i) → Γ₁' V ≈ᵥ Γ₁' V'
Γ₁-cong' V=V' = ⊕ᵥ-cong (⟦_⟧-cong' V=V') (≈ᵥ-refl {~ I})

-- TODO: Implement this using the [_,_]_ instead.
Γ₁∥ : AsyncIterable _ _ _
Γ₁∥ = record {
  Sᵢ   = const RoutingSet;
  _≈ᵢ_ = _↭_;
  F    = Γ₁;
  isAsyncIterable = record {
    isDecEquivalenceᵢ = isDecEquivalenceᵢ;
    F-cong = Γ₁-cong
    }
  }
  where open IndexedDecSetoid ≈ᵥ-decSetoidᵢ

Ω₁' : Schedule n → RoutingVector → {t : 𝕋} → Acc _<_ t → RoutingVector
Ω₁' = asyncIter' Γ₁∥

Ω₁ : Schedule n → RoutingVector → 𝕋 → RoutingVector
Ω₁ ψ V t = Ω₁' ψ V (<-wellFounded t)

-- Schedule reduction Ω₁ → Ω₀
r₁ : ∀ {n} → Schedule n → Schedule n
r₁ = id

-- Lemmas
-- Maybe try to merely have a unique destination postulate for RoutingVectors
postulate
  ~-─-inverse : ∀ V → ~(─ V) ≈ᵥ V -- requires uniqueness of destination
  ─-~-inverse : ∀ X → ─(~ X) ≈ₘ X
  ─-cong : ∀ {U V} → U ≈ᵥ V → ─ U ≈ₘ ─ V -- requires uniqueness of destination

─-⊕-distributive : ∀ U V → ─ (U ⊕ᵥ V) ≈ₘ (─ U) ⊕ₘ (─ V)
─-⊕-distributive U V = begin
  ─ (U ⊕ᵥ V)               ≈⟨ ─-cong (⊕ᵥ-cong (≈ᵥ-sym (~-─-inverse U)) (≈ᵥ-sym (~-─-inverse V))) ⟩
  ─ ((~(─ U)) ⊕ᵥ (~(─ V))) ≈⟨ ─-cong (≈ᵥ-sym (⊕-distributive (─ U) (─ V))) ⟩
  ─ (~ ((─ U) ⊕ₘ (─ V)))   ≈⟨ ─-~-inverse ((─ U) ⊕ₘ (─ V)) ⟩
  (─ U) ⊕ₘ (─ V) ∎
  where open EqReasoning ℝ𝕄ₛ

─-〚_〛-distributive : ∀ A V → ─ (A 〚 V 〛) ≈ₘ A 〔 ─ V 〕
─-〚_〛-distributive A V = begin
  ─ (A 〚 V 〛)       ≈⟨ ─-cong (〚〛-cong (≈ᵥ-sym (~-─-inverse V))) ⟩
  ─ (A 〚 ~(─ V) 〛)  ≈⟨ ─-cong Lemma-Γ₀=Γ₁ ⟩
  ─ (~ (A 〔 ─ V 〕)) ≈⟨ ─-~-inverse (A 〔 ─ V 〕) ⟩
  A 〔 ─ V 〕 ∎
  where open EqReasoning ℝ𝕄ₛ

-- Theorem 3 (dual)
Γ₀=Γ₁-dual : ∀ V → ─(Γ₁ V) ≈ₘ Γ₀ (─ V)
Γ₀=Γ₁-dual V = begin
  ─(Γ₁ V)            ≡⟨⟩
  ─(A 〚 V 〛 ⊕ᵥ ~ I) ≈⟨ ─-⊕-distributive (A 〚 V 〛) (~ I) ⟩
  ─(A 〚 V 〛) ⊕ₘ ─(~ I) ≈⟨ ⊕ₘ-cong (─-〚_〛-distributive A V) (─-~-inverse I) ⟩
  A 〔 ─ V 〕 ⊕ₘ I ≡⟨⟩
  Γ₀ (─ V) ∎
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
-- TODO: Represent Ω₁ using the [_,_]_ operator
module _ (ψ : Schedule n) where
  open Schedule ψ
  
  Ω₁'=Ω₀' : ∀ V {t} (accₜ : Acc _<_ t) → ─ (Ω₁' ψ V accₜ) ≈ₘ Ω₀' (r₁ ψ) (─ V) accₜ
  Ω₁'=Ω₀' V {zero}  _           = ≈ₘ-refl
  Ω₁'=Ω₀' V {suc t} (acc rec) i with i ∈? α (suc t)
  ... | no _ = Ω₁'=Ω₀' V (rec t ≤-refl) i
  ... | yes _ = prf
    where β̂< : ∀ j → β (suc t) i j < suc t
          β̂< j = s≤s (β-causality t i j)
          prf : (─ (Γ₁ λ j → Ω₁' ψ V (rec (β (suc t) i j) (β̂< j)) j)) i ≈ₜ (Γ₀ λ j → Ω₀' ψ (─ V) (rec (β (suc t) i j) (β̂< j)) j) i
          prf = begin
           (─ (Γ₁ λ j → (Ω₁' ψ V (rec (β (suc t) i j) (β̂< j))) j)) i ≈⟨ Γ₀=Γ₁-dual (λ j → (Ω₁' ψ V (rec (β (suc t) i j) (β̂< j))) j) i ⟩
           (Γ₀ (─ λ j → (Ω₁' ψ V (rec (β (suc t) i j) (β̂< j))) j)) i ≈⟨ (Γ₀-cong λ j → Ω₁'=Ω₀' V (rec (β (suc t) i j) (β̂< j)) j) i ⟩
           (Γ₀ λ j → (Ω₀' ψ (─ V) (rec (β (suc t) i j) (β̂< j))) j) i ∎
           where open EqReasoning ℝ𝕋ₛ

Ω₁=Ω₀ : ∀ ψ V t → ─ (Ω₁ ψ V t) ≈ₘ Ω₀ (r₁ ψ) (─ V) t
Ω₁=Ω₀ ψ V t = Ω₁'=Ω₀' ψ V (<-wellFounded t)

Ω₁ˢʸⁿᶜ=Γ₁ : ∀ V t → Ω₁ ψˢʸⁿᶜ V t ≈ᵥ (Γ₁ ^ t) V
Ω₁ˢʸⁿᶜ=Γ₁ = ψˢʸⁿᶜ-isSynchronous Γ₁∥
