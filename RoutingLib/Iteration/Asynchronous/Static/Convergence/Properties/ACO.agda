--------------------------------------------------------------------------
-- A module that extracts some very basic auxiallary properties from the
-- definition of an ACO
--------------------------------------------------------------------------

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO
  {a ℓ ℓ₂ ℓ₃ n}
  (I∥ : AsyncIterable a ℓ n)
  {X₀ : IPred _ ℓ₃}
  (aco : PartialACO I∥ X₀ ℓ₂)
  where

open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Data.Product

open import RoutingLib.Function
open import RoutingLib.Function.Reasoning
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous

open AsyncIterable I∥
open PartialACO aco

--------------------------------------------------------------------------
-- Deconstructing the assumption D-finish

k*≤k⇒x*∈D[k] : ∀ {k} → k* ≤ k → x* ∈ᵢ D k
k*≤k⇒x*∈D[k] k*≤k = proj₁ (D-finish k*≤k)

x*∈D[k*] : x* ∈ᵢ D k* 
x*∈D[k*] = k*≤k⇒x*∈D[k] ≤-refl

k*≤k⇒x∈D[k]⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ D k → x ≈ x* 
k*≤k⇒x∈D[k]⇒x≈x* k*≤k = proj₂ (D-finish k*≤k)

x∈D[k*]⇒x≈x* : ∀ {x} → x ∈ᵢ D k* → x ≈ x* 
x∈D[k*]⇒x≈x* = k*≤k⇒x∈D[k]⇒x≈x* ≤-refl

x*-fixed : F x* ≈ x*
x*-fixed = begin⟨ x*∈D[k*] ⟩
  ∴ x*   ∈ᵢ D k*       $⟨ F-mono-D ⟩
  ∴ F x* ∈ᵢ D (suc k*) $⟨ k*≤k⇒x∈D[k]⇒x≈x* (n≤1+n k*) ⟩
  ∴ F x* ≈ x*          ∎

--------------------------------------------------------------------------
-- Synchronous iterations

Fᵏx∈D₀ : ∀ k {x} → x ∈ᵢ D 0 → (F ^ k) x ∈ᵢ D 0
Fᵏx∈D₀ zero    x∈D₀ = x∈D₀
Fᵏx∈D₀ (suc k) x∈D₀ = F-resp-D₀ (Fᵏx∈D₀ k x∈D₀)

Fᵏx∈Dₖ : ∀ k {x} → x ∈ᵢ D 0 → (F ^ k) x ∈ᵢ D k
Fᵏx∈Dₖ zero    x∈D₀ = x∈D₀
Fᵏx∈Dₖ (suc k) x∈D₀ = F-mono-D (Fᵏx∈Dₖ k x∈D₀)

--------------------------------------------------------------------------
-- If `D 0` is non-empty then it can be shown that the fixed point is in
-- every box `D k`

x*∈D₀ : ∀ {x} → x ∈ᵢ D 0 → x* ∈ᵢ D 0
x*∈D₀ {x} x∈D₀ = begin⟨ x∈D₀ ⟩
  ∴ x ∈ᵢ D 0            $⟨ Fᵏx∈Dₖ k* ⟩
  ∴ (F ^ k*) x ∈ᵢ D k*  $⟨ x∈D[k*]⇒x≈x* ⟩
  ∴ (F ^ k*) x ≈ x*     $⟨ D-cong ◌ (Fᵏx∈D₀ k* x∈D₀) ⟩
  ∴ x* ∈ᵢ D 0           ∎

x*∈Dₖ : ∀ {x} → x ∈ᵢ D 0 → ∀ k → x* ∈ᵢ D k
x*∈Dₖ x∈D₀ zero    = x*∈D₀ x∈D₀
x*∈Dₖ x∈D₀ (suc k) = begin⟨ x*∈Dₖ x∈D₀ k ⟩
  ∴ x*   ∈ᵢ D k        $⟨ F-mono-D ⟩
  ∴ F x* ∈ᵢ D (suc k)  $⟨ D-cong x*-fixed ⟩
  ∴ x*   ∈ᵢ D (suc k)  ∎
