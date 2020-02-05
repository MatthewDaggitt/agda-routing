open import Data.Nat using (ℕ; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Fin using (Fin)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing using (AdjacencyMatrix; RoutingMatrix)

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets
  {a b ℓ n-1}
  {algebra          : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra    : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  where

open import Data.Nat.Properties using (+-comm; +-assoc)
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (∁; U; Decidable)
  renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Data.Path.CertifiedI.All
open import RoutingLib.Data.Path.CertifiedI.Properties

import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude

open Prelude isRoutingAlgebra isPathAlgebra A

------------------------------------------------------------------------------
-- Fixed vertices -- vertices that don't change their value after time t

𝓕 : 𝕋 → Vertex → Set _
𝓕 t i = ∀ s → σ (t + s) X i j ≈ σ t X i j

j∈𝓕₁ : j ∈ᵤ 𝓕 1
j∈𝓕₁ s = FXᵢᵢ≈FYᵢᵢ (σ s X) X refl

𝓕ₜ⊆𝓕ₜ₊ₛ : ∀ t s {i} → i ∈ᵤ 𝓕 t → i ∈ᵤ 𝓕 (t + s)
𝓕ₜ⊆𝓕ₜ₊ₛ t s {i} i∈Fₜ r = begin
  σ ((t + s) + r) X i j  ≡⟨ cong (λ t → σ t X i j) (+-assoc t s r) ⟩
  σ (t + (s + r)) X i j  ≈⟨ i∈Fₜ (s + r) ⟩
  σ t             X i j  ≈⟨ ≈-sym (i∈Fₜ s)  ⟩
  σ (t + s) X i j        ∎
  where open EqReasoning S

𝓕-alignment : ∀ t {i} → i ∈ᵤ 𝓕 t → ∀ {k l p e⇿p i∉p} →
                    path (σ t X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                    i ≡ l × σ t X i j ≈ A i k ▷ σ t X k j ×
                    path (σ t X k j) ≈ₚ valid p
𝓕-alignment t {i} i∈Sₜ p[σXᵢⱼ]≈uv∷p
  with ≈-reflexive (cong (λ t → σ t X i j) (+-comm 1 t))
... | σ¹⁺ᵗ≈σᵗ⁺¹ with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t X) i j (≈ₚ-trans (path-cong (≈-trans σ¹⁺ᵗ≈σᵗ⁺¹ (i∈Sₜ 1))) p[σXᵢⱼ]≈uv∷p)
...   | i≡l , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p = i≡l , ≈-trans (≈-sym (i∈Sₜ 1)) (≈-trans (≈-sym σ¹⁺ᵗ≈σᵗ⁺¹) σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ) , p[σᵗXₖⱼ]≈p

------------------------------------------------------------------------------
-- Converged nodes -- nodes for which all nodes they route through are fixed
-- after time t

𝓒 : 𝕋 → Vertex → Set _
𝓒 t i = i ∈ᵤ 𝓕 t × Allᵥ (𝓕 t) (path (σ t X i j))

𝓒-cong : ∀ {s t k} → k ∈ᵤ 𝓒 s → s ≡ t → k ∈ᵤ 𝓒 t
𝓒-cong k∈Fₛ refl = k∈Fₛ

j∈𝓒₁ : j ∈ᵤ 𝓒 1
j∈𝓒₁ = j∈𝓕₁ , Allᵥ-resp-≈ₚ (valid []) (≈ₚ-sym (begin
  path (F X j j) ≈⟨ path-cong (FXᵢᵢ≈Iᵢᵢ X j) ⟩
  path (I j j)   ≡⟨ cong path (Iᵢᵢ≡0# j) ⟩
  path 0#        ≈⟨ p[0]≈[] ⟩
  valid []       ∎))
  where open EqReasoning (ℙₛ n)

𝓒ₜ⊆𝓒ₜ₊ₛ : ∀ t s → 𝓒 t ⊆ᵤ 𝓒 (t + s)
𝓒ₜ⊆𝓒ₜ₊ₛ t s (i∈Sₜ , p∈Sₜ) =
  𝓕ₜ⊆𝓕ₜ₊ₛ t s i∈Sₜ ,
  mapᵥ (𝓕ₜ⊆𝓕ₜ₊ₛ t s) (Allᵥ-resp-≈ₚ p∈Sₜ (path-cong (≈-sym (i∈Sₜ s))) )

𝓒ₜ⊆𝓒ₛ₊ₜ : ∀ t s → 𝓒 t ⊆ᵤ 𝓒 (s + t)
𝓒ₜ⊆𝓒ₛ₊ₜ t s rewrite +-comm s t = 𝓒ₜ⊆𝓒ₜ₊ₛ t s

𝓒-path : ∀ t {i p} → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓒 t → Allᵥ (𝓒 t) p
𝓒-path t {i} {invalid}  _ _ = invalid
𝓒-path t {i} {valid []} _ _ = valid []
𝓒-path t {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p i∈𝓒ₜ@(i∈𝓕ₜ , ik∷p∈𝓕ₜ)
  with 𝓒-path t {k} {valid p} | 𝓕-alignment t i∈𝓕ₜ p[σᵗXᵢⱼ]≈ik∷p
... | rec | refl , _ , p[σᵗXₖⱼ]≈p with Allᵥ-resp-≈ₚ ik∷p∈𝓕ₜ p[σᵗXᵢⱼ]≈ik∷p
...   | (valid ([ _ , k∈𝓕ₜ ]∷ p∈𝓕ₜ)) with Allᵥ-resp-≈ₚ (valid p∈𝓕ₜ) (≈ₚ-sym p[σᵗXₖⱼ]≈p)
...     | k∈𝓒ₜ with rec p[σᵗXₖⱼ]≈p (k∈𝓕ₜ , k∈𝓒ₜ)
...       | valid p∈𝓒ₜ = valid ([ i∈𝓒ₜ , (k∈𝓕ₜ , k∈𝓒ₜ) ]∷ p∈𝓒ₜ)

𝓒-eq : ∀ t k s₁ s₂ → k ∈ᵤ 𝓒 t → σ (t + s₁) X k j ≈ σ (t + s₂) X k j
𝓒-eq t k s₁ s₂ (k∈Sₜ , _) = begin
  σ (t + s₁) X k j ≈⟨ k∈Sₜ s₁ ⟩
  σ (t)      X k j ≈⟨ ≈-sym (k∈Sₜ s₂) ⟩
  σ (t + s₂) X k j ∎
  where open EqReasoning S

------------------------------------------------------------------------------
-- Aligned edges

Aligned : 𝕋 → Edge → Set _
Aligned t (i , k) = σ t X i j ≈ A i k ▷ σ t X k j

Aligned? : ∀ t → Decidable (Aligned t)
Aligned? t (i , k) = σ t X i j ≟ A i k ▷ σ t X k j

------------------------------------------------------------------------------
-- Real nodes -- Nodes that are using paths that are consistent with the
-- current routing choices of the other nodes in the network.

𝓡 : 𝕋 → Vertex → Set ℓ
𝓡 t i = Allₑ (Aligned t) (path (σ t X i j))

𝓡? : ∀ t → Decidable (𝓡 t)
𝓡? t i = allₑ? (Aligned? t) (path (σ t X i j))

𝓡-cong : ∀ {s t k} → k ∈ᵤ 𝓡 s → s ≡ t → k ∈ᵤ 𝓡 t
𝓡-cong k∈Rₛ refl = k∈Rₛ

¬𝓡-cong : ∀ {s t k} → k ∉ᵤ 𝓡 s → s ≡ t → k ∉ᵤ 𝓡 t
¬𝓡-cong k∉Rₛ refl = k∉Rₛ

𝓡-alignment : ∀ t {i} → i ∈ᵤ 𝓡 (suc t) → ∀ {k l p e⇿p i∉p} →
                 path (σ (suc t) X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                 i ≡ l × σ (suc t) X i j ≈ A i k ▷ σ (suc t) X k j ×
                 path (σ (suc t) X k j) ≈ₚ valid p
𝓡-alignment t {i} i∈R₁₊ₜ {k} p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
  with Allₑ-resp-≈ₚ i∈R₁₊ₜ p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
... | valid (σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ ∷ _)
    with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t X) i j p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
...   | refl , _ , _
      with alignPathExtension (σ (suc t) X) i j k
        (≈ₚ-trans (path-cong (≈-sym σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ)) p[σ¹⁺ᵗXᵢⱼ]≈uv∷p)
...     | _ , _ , p[σ¹⁺ᵗXₖⱼ]≈p = refl , σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ , p[σ¹⁺ᵗXₖⱼ]≈p


𝓡-path : ∀ {t i p} → path (σ (suc t) X i j) ≈ₚ p →
        i ∈ᵤ 𝓡 (suc t) → Allᵥ (𝓡 (suc t)) p
𝓡-path {_} {i} {invalid}  _ _ = invalid
𝓡-path {_} {i} {valid []} _ _ = valid []
𝓡-path {t} {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈vk∷p i∈R₁₊ₜ
  with 𝓡-path {t} {k} {valid p} | Allₑ-resp-≈ₚ i∈R₁₊ₜ p[σᵗXᵢⱼ]≈vk∷p
... | rec | valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pʳ) with 𝓡-alignment t i∈R₁₊ₜ p[σᵗXᵢⱼ]≈vk∷p
...   | refl , _ , p[σ¹⁺ᵗXₖⱼ]≈p with Allₑ-resp-≈ₚ (valid pʳ) (≈ₚ-sym p[σ¹⁺ᵗXₖⱼ]≈p)
...     | k∈R₁₊ₜ with rec p[σ¹⁺ᵗXₖⱼ]≈p k∈R₁₊ₜ
...       | valid allpʳ = valid ([ i∈R₁₊ₜ , k∈R₁₊ₜ ]∷ allpʳ)

𝓡-∅ : ∀ t i → path (σ t X i j) ≈ₚ invalid → i ∈ᵤ 𝓡 t
𝓡-∅ _ _ p≡∅ = Allₑ-resp-≈ₚ invalid (≈ₚ-sym p≡∅)

𝓡-[] : ∀ t i → path (σ t X i j) ≈ₚ valid [] → i ∈ᵤ 𝓡 t
𝓡-[] _ _ p≡[] = Allₑ-resp-≈ₚ (valid []) (≈ₚ-sym p≡[])

¬𝓡-length : ∀ t i → i ∉ᵤ 𝓡 t → 1 ≤ size (σ t X i j)
¬𝓡-length t i i∉Rₜ with path (σ t X i j)
... | invalid               = contradiction invalid i∉Rₜ
... | valid []              = contradiction (valid []) i∉Rₜ
... | valid (e ∷ p ∣ _ ∣ _) = s≤s z≤n

¬𝓡-retraction : ∀ t i → i ∉ᵤ 𝓡 (suc t) → ∃₂ λ k p → ∃₂ λ k∉p e↔p →
                path (σ (suc t) X i j) ≈ₚ valid ((i , k) ∷ p ∣ k∉p ∣ e↔p) ×
                σ (suc t) X i j ≈ A i k ▷ σ t X k j ×
                path (σ t X k j) ≈ₚ valid p
¬𝓡-retraction t i i∉R₁₊ₜ with path (σ (suc t) X i j) | inspect path (σ (suc t) X i j)
... | invalid  | _ = contradiction invalid i∉R₁₊ₜ
... | valid [] | _ = contradiction (valid []) i∉R₁₊ₜ
... | valid ((_ , k) ∷ p ∣ k∉p ∣ e↔p) | [ p[σ¹⁺ᵗ]≡ik∷p ]
  with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t X) i j (≈ₚ-reflexive p[σ¹⁺ᵗ]≡ik∷p)
...   | refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p =
  k , p , k∉p , e↔p , ≈ₚ-refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p

𝓒ₜ⊆𝓡ₜ : ∀ t {i p} → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓒 t → i ∈ᵤ 𝓡 t
𝓒ₜ⊆𝓡ₜ t {i} {invalid}  p[σᵗXᵢⱼ]≈∅  _ = 𝓡-∅ t i p[σᵗXᵢⱼ]≈∅
𝓒ₜ⊆𝓡ₜ t {i} {valid []} p[σᵗXᵢⱼ]≈[] _ = 𝓡-[] t i p[σᵗXᵢⱼ]≈[]
𝓒ₜ⊆𝓡ₜ t {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
  with 𝓒ₜ⊆𝓡ₜ t {k} {valid p} | 𝓕-alignment t i∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
... | rec | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p with 𝓒-path t p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
...   | valid ([ _ , k∈Fₜ ]∷ p∈Fₜ) with rec p[σᵗXₖⱼ]≈p k∈Fₜ
...     | k∈Rₜ with Allₑ-resp-≈ₚ k∈Rₜ p[σᵗXₖⱼ]≈p
...       | valid pˡ = Allₑ-resp-≈ₚ (valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pˡ)) (≈ₚ-sym p[σᵗXᵢⱼ]≈ik∷p)

¬𝓡⊆¬𝓒 : ∀ {t i} → i ∉ᵤ 𝓡 t → i ∉ᵤ 𝓒 t
¬𝓡⊆¬𝓒 {t} {i} i∉Rₜ i∈Fₜ = i∉Rₜ (𝓒ₜ⊆𝓡ₜ t ≈ₚ-refl i∈Fₜ)
