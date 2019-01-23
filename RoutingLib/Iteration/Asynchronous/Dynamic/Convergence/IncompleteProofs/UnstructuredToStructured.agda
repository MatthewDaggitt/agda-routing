open import Data.Fin using (Fin; zero)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO)
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO as ACOProperties
open import RoutingLib.Relation.Unary.Indexed hiding (_∉_)

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.UnstructuredToStructured
  {a ℓ n-1 p} (𝓘 : AsyncIterable a ℓ (suc n-1)) (aco : ACO 𝓘 p) where

open AsyncIterable 𝓘
open ACO aco

n : ℕ
n = suc n-1

module _ (e : Epoch) (q : Subset n) where

  open ACOProperties 𝓘 aco e q

  B′ : ℕ → IPred Sᵢ p
  B′ = B e q

  F′ : S → S
  F′ = F e q

  σ : ℕ → S → S
  σ zero    x = x
  σ (suc i) x = F′ (σ i x)


  -- Fixed points







  C : ℕ → IPred Sᵢ p
  C zero    = B′ 0
  C (suc k) = B′ k ∩ B′ (suc k)

  Cₖ⊆Bₖ : ∀ k → C k ⊆[ Sᵢ ] B′ k
  Cₖ⊆Bₖ zero    x∈C₀   = x∈C₀
  Cₖ⊆Bₖ (suc k) x∈C₁₊ₖ = proj₂ ∘ x∈C₁₊ₖ

  k*≤k⇒x*∈Cᵏ : ∀ {k} → k* ≤ k → x* ∈ C k
  k*≤k⇒x*∈Cᵏ {zero}  k*≤0   i = x*∈Bₖ {!!} 0 i
  k*≤k⇒x*∈Cᵏ {suc k} k*≤1+k i = x*∈Bₖ {!!} k i , x*∈Bₖ {!!} (suc k) i

  k*≤k∧x∈Cᵏ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ C k → x ≈ x*
  k*≤k∧x∈Cᵏ⇒x≈x* {zero}  k*≤0   x∈C₀   i = k*≤k∧x∈Bₖ⇒x≈x* k*≤0 x∈C₀ i
  k*≤k∧x∈Cᵏ⇒x≈x* {suc k} k*≤1+k x∈C₁₊ₖ i = k*≤k∧x∈Bₖ⇒x≈x* k*≤1+k (proj₂ ∘ x∈C₁₊ₖ) i

  C-finish : ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ C k × (∀ {x} → x ∈ C k → x ≈ x*))
  C-finish = k* , x* , (λ k*≤k → k*≤k⇒x*∈Cᵏ k*≤k , k*≤k∧x∈Cᵏ⇒x≈x* k*≤k)

  C-null : ∀ {k i} → i ∉ q → ⊥ i ∈ᵤ C k i
  C-null {zero}  i∉q = B-null i∉q
  C-null {suc k} i∉q = B-null i∉q , B-null i∉q

  F-resp-C₀ : ∀ {x} → x ∈ C 0 → F′ x ∈ C 0
  F-resp-C₀ = F-resp-B₀

  F-mono-C : ∀ {k x} → WellFormed q x → x ∈ C k → F′ x ∈ C (suc k)
  F-mono-C {zero}  x-wf x∈C₀   i = F-resp-B₀ x∈C₀ i , F-mono-B {!!} x∈C₀ i
  F-mono-C {suc k} x-wf x∈C₁₊ₖ i = F-mono-B {!!} (proj₁ ∘ x∈C₁₊ₖ) i , F-mono-B {!!} (proj₂ ∘ x∈C₁₊ₖ) i

  C₁₊ₖ⊆Cₖ : ∀ k → C (suc k) ⊆[ Sᵢ ] C k
  C₁₊ₖ⊆Cₖ zero    x∈C₁   i = proj₁ (x∈C₁ i)
  C₁₊ₖ⊆Cₖ (suc k) x∈C₂₊ₖ i = {!!} , proj₁ (x∈C₂₊ₖ i)

nested-aco : ACO 𝓘 p
nested-aco = record
  { B         = C
  ; B₀-eqᵢ    = {!!}
  ; Bᵢ-cong   = {!!}
  ; B-finish  = C-finish
  ; B-null    = λ {e p k} → C-null e p {k}
  ; F-resp-B₀ = λ {e p} → F-resp-C₀ e p
  ; F-mono-B  = λ {e p} → F-mono-C e p
  }
