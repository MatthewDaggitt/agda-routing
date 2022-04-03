open import Data.Fin using (Fin)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Nat as ℕ using (ℕ; zero; suc; pred; z≤n; s≤s; _+_; _^_; _∸_; _*_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Unit using ()
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤ᵤ)
open import Data.Empty.Polymorphic using (⊥-elim) renaming (⊥ to ⊥ᵤ)
open import Data.Product as Product using (∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; flip; case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)

import RoutingLib.Function.Reasoning as FunctionalReasoning
open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Fin.Subset.Induction

open import RoutingLib.Routing.Prelude using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step3_DangerousNodes as Step3_DangerousNodes
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step4_InductiveStep as Step4_InductiveStep
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step5_Distributivity as Step5_Distributivity

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step6_Proof
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  where

open Prelude isRoutingAlgebra isPathAlgebra A renaming (𝑪ₘ′ to Consistent)

------------------------------------------------------------------------
-- Increasing proof

increasing⇒n²-convergence : IsIncreasing algebra →
                            ∀ X t → σ (n ^ 2 + t) X ≈ₘ σ (n ^ 2) X
increasing⇒n²-convergence isIncreasing X t i j = proj₁ (convergesIn-n² i) t
  where
  open Step1_NodeSets          isRoutingAlgebra isPathAlgebra A X j
  open Step2_ConvergedSubtree  isRoutingAlgebra isPathAlgebra A X j using (iₘᵢₙ; iₘᵢₙ∉C)
  open Step3_DangerousNodes    isRoutingAlgebra isPathAlgebra A X j using (eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe)
  open Step4_InductiveStep     isRoutingAlgebra isPathAlgebra A X j using (iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ)
  
  f : ℕ → ℕ
  f t = 1 + t * n

  f-mono-≤ : f Preserves _≤_ ⟶ _≤_
  f-mono-≤ = +-monoʳ-≤ 1 ∘ *-monoˡ-≤ n

  f[n-1]≤n² : f n-1 ≤ n ^ 2
  f[n-1]≤n² rewrite *-identityʳ n-1 = +-monoʳ-≤ 1 (m≤n+m (n-1 * n) n-1)

  f[1+t]≡f[t]+n : ∀ t → f (suc t) ≡ f t + n
  f[1+t]≡f[t]+n t rewrite +-comm (t * n) n = refl
  
  P : ℕ → Pred (Fin n) _
  P zero    i = ⊥ᵤ
  P (suc t) i = i ∈ᵤ 𝓒 (f t)
  
  P-mono-≤ : ∀ {t s} → t ≤ s → P t ⊆ᵤ P s
  P-mono-≤ (s≤s t≤s) = 𝓒-mono-≤ (f-mono-≤ t≤s)
  
  Pₜ⊆Pₜ₊₁ : ∀ {t} → P t ⊆ᵤ P (suc t)
  Pₜ⊆Pₜ₊₁ {t} = P-mono-≤ (n≤1+n t)

  next : (t : ℕ) (s : Subset n) → Nonfull s → Fin n
  next t s nf with j ∈? s
  ... | yes j∈s = iₘᵢₙ (f (t ∸ 1)) s nf j∈s
  ... | no  j∉s = j

  next∉ : (t : ℕ) (s : Subset n) (nf : Nonfull s) → next t s nf ∉ s
  next∉ t s nf with j ∈? s
  ... | yes j∈s = iₘᵢₙ∉C (f (t ∸ 1)) s nf j∈s
  ... | no  j∉s = j∉s

  P[next] : (t : ℕ) (s : Subset n) (nf : Nonfull s) → All (P t) s → next t s nf ∈ᵤ P (suc t)
  P[next] t s nf Ps with j ∈? s | t
  ... | no  j∉s | t     = j∈𝓒ₜ (f t)
  ... | yes j∈s | zero  = ⊥-elim (Ps j∈s)
  ... | yes j∈s | suc t = begin⟨ iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ (f t) s nf j∈s Ps n-1 (eₘᵢₙ≤ₜ₊ₙ₋₁₊ₛe isIncreasing (f t) s nf j∈s Ps) ⟩
    ∴ iₘᵢₙ (f t) s nf j∈s ∈ᵤ 𝓒 (f t + n)   $⟨ flip 𝓒-cong (sym (f[1+t]≡f[t]+n t)) ⟩
    ∴ iₘᵢₙ (f t) s nf j∈s ∈ᵤ 𝓒 (f (suc t)) ∎
    where open FunctionalReasoning
  
  convergesIn-1+[n-1]*n : ∀ i → i ∈ᵤ 𝓒 (1 + n-1 * n)
  convergesIn-1+[n-1]*n = positiveOneByOne-induction P (record
    { next    = next
    ; next∉   = next∉
    ; P[next] = P[next]
    ; Pₜ⊆Pₜ₊₁ = Pₜ⊆Pₜ₊₁
    })

  convergesIn-n² : ∀ i → i ∈ᵤ 𝓒 (n ^ 2)
  convergesIn-n² i = begin⟨ convergesIn-1+[n-1]*n i ⟩
    ∴ i ∈ᵤ 𝓒 (f n-1) $⟨ 𝓒-mono-≤ f[n-1]≤n² ⟩
    ∴ i ∈ᵤ 𝓒 (n ^ 2) ∎
    where open FunctionalReasoning



------------------------------------------------------------------------
-- Distributive + increasing proof

increasing+distrib⇒n-convergence : IsIncreasing algebra →
                                   IsDistributive algebra →
                                   ∀ X → Consistent X →
                                   ∀ t → σ (n + t) X ≈ₘ σ n X
increasing+distrib⇒n-convergence isIncreasing distrib X Xᶜ t i j = proj₁ (convergesIn-n i) t
  where
  open Step1_NodeSets          isRoutingAlgebra isPathAlgebra A X j
  open Step2_ConvergedSubtree  isRoutingAlgebra isPathAlgebra A X j using (iₘᵢₙ; iₘᵢₙ∉C)
  open Step4_InductiveStep     isRoutingAlgebra isPathAlgebra A X j using (iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ)
  open Step5_Distributivity    isRoutingAlgebra isPathAlgebra A X j using (iₘᵢₙ∈𝓖₁₊ₜ; eₘᵢₙ≤ₜ₊ₛe)

  ∈𝓚 : ∀ s i → i ∈ᵤ 𝓚 s
  ∈𝓚 s i = σ-pres-𝑪ₘ (proj₁ Xᶜ) s i j ,
           σ-pres-⇨[]⇨ X (λ k l → proj₁ (proj₂ Xᶜ k l)) s i j ,
           σ-pres-p[X]ᵢᵢ≈[] X (λ {k} {l} → proj₂ (proj₂ Xᶜ k l)) s
   
  P : ℕ → Pred (Fin n) _
  P zero    i = ⊥ᵤ
  P (suc t) i = i ∈ᵤ 𝓒 t × i ∈ᵤ 𝓖 t
  
  P-mono-≤ : ∀ {t s} → t ≤ s → P t ⊆ᵤ P s
  P-mono-≤ (s≤s t≤s) = Product.map (𝓒-mono-≤ t≤s) (𝓖-mono-≤ t≤s)
  
  Pₜ⊆Pₜ₊₁ : ∀ {t} → P t ⊆ᵤ P (suc t)
  Pₜ⊆Pₜ₊₁ {t} = P-mono-≤ (n≤1+n t)

  next : (t : ℕ) (s : Subset n) → Nonfull s → Fin n
  next t s nf with j ∈? s
  ... | yes j∈s = iₘᵢₙ (t ∸ 1) s nf j∈s
  ... | no  j∉s = j

  next∉ : (t : ℕ) (s : Subset n) (nf : Nonfull s) → next t s nf ∉ s
  next∉ t s nf with j ∈? s
  ... | yes j∈s = iₘᵢₙ∉C (t ∸ 1) s nf j∈s
  ... | no  j∉s = j∉s

  P[next] : (t : ℕ) (s : Subset n) (nf : Nonfull s) → All (P t) s → next t s nf ∈ᵤ P (suc t)
  P[next] t s nf Ps with j ∈? s | t
  ... | no  j∉s | t     = j∈𝓚⇒j∈𝓒 t (∈𝓚 t j) , j∈𝓚⇒j∈𝓖 t (∈𝓚 t j)
  ... | yes j∈s | zero  = ⊥-elim (Ps j∈s)
  ... | yes j∈s | suc t =
    (begin⟨ iₘᵢₙ∈𝓒ₜ₊ₜⁱⁿᶜ t s nf j∈s (proj₁ ∘ Ps) 0
      (eₘᵢₙ≤ₜ₊ₛe isIncreasing distrib t s nf j∈s (λ s → ∈𝓚 (t + s)) (proj₁ ∘ Ps) (proj₂ ∘ Ps)) ⟩
      ∴ iₘᵢₙ t s nf j∈s ∈ᵤ 𝓒 (t + 1) $⟨ flip 𝓒-cong (+-comm t 1) ⟩
      ∴ iₘᵢₙ t s nf j∈s ∈ᵤ 𝓒 (1 + t) ∎)
    , iₘᵢₙ∈𝓖₁₊ₜ isIncreasing distrib t s nf j∈s (λ s → ∈𝓚 (t + s)) (proj₁ ∘ Ps) (proj₂ ∘ Ps)
    where open FunctionalReasoning
  
  convergesIn-n-1 : ∀ i → i ∈ᵤ 𝓒 n-1
  convergesIn-n-1 = proj₁ ∘ positiveOneByOne-induction P (record
    { next      = next
    ; next∉     = next∉
    ; P[next]   = P[next]
    ; Pₜ⊆Pₜ₊₁   = Pₜ⊆Pₜ₊₁
    })

  convergesIn-n : ∀ i → i ∈ᵤ 𝓒 n
  convergesIn-n i = begin⟨ convergesIn-n-1 i ⟩
    ∴ i ∈ᵤ 𝓒 n-1 $⟨ 𝓒-mono-≤ (n≤1+n n-1) ⟩
    ∴ i ∈ᵤ 𝓒 n   ∎
    where open FunctionalReasoning
