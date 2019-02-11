--------------------------------------------------------------------------
-- A module that extracts some very basic auxiallary properties from the
-- definition of an ACO
--------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO
  {a ℓ ℓ₃ n}
  (I∥ : AsyncIterable a ℓ n)
  (aco : ACO I∥ ℓ₃)
  where

open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Data.Product

open import RoutingLib.Function
open import RoutingLib.Function.Reasoning
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous

open AsyncIterable I∥
open ACO aco

--------------------------------------------------------------------------
-- Deconstructing the assumption B-finish

k* : ℕ
k* = proj₁ (B-finish)

x* : S
x* = proj₁ (proj₂ B-finish)

k*≤k⇒x*∈B[k] : ∀ {k} → k* ≤ k → x* ∈ᵢ B k
k*≤k⇒x*∈B[k] k*≤k = proj₁ (proj₂ (proj₂ B-finish) k*≤k)

x*∈B[k*] : x* ∈ᵢ B k* 
x*∈B[k*] = k*≤k⇒x*∈B[k] ≤-refl

k*≤k⇒x∈B[k]⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x* 
k*≤k⇒x∈B[k]⇒x≈x* k*≤k = proj₂ (proj₂ (proj₂ B-finish) k*≤k)

x∈B[k*]⇒x≈x* : ∀ {x} → x ∈ᵢ B k* → x ≈ x* 
x∈B[k*]⇒x≈x* = k*≤k⇒x∈B[k]⇒x≈x* ≤-refl

x*-fixed : F x* ≈ x*
x*-fixed = begin⟨ x*∈B[k*] ⟩
  ⇒ x*   ∈ᵢ B k*       ∴⟨ F-mono-B ⟩
  ⇒ F x* ∈ᵢ B (suc k*) ∴⟨ k*≤k⇒x∈B[k]⇒x≈x* (n≤1+n k*) ⟩
  ⇒ F x* ≈ x*          ∎

--------------------------------------------------------------------------
-- Synchronous iterations

Fᵏx∈B₀ : ∀ k {x} → x ∈ᵢ B 0 → (F ^ k) x ∈ᵢ B 0
Fᵏx∈B₀ zero    x∈B₀ = x∈B₀
Fᵏx∈B₀ (suc k) x∈B₀ = F-resp-B₀ (Fᵏx∈B₀ k x∈B₀)

Fᵏx∈Bₖ : ∀ k {x} → x ∈ᵢ B 0 → (F ^ k) x ∈ᵢ B k
Fᵏx∈Bₖ zero    x∈B₀ = x∈B₀
Fᵏx∈Bₖ (suc k) x∈B₀ = F-mono-B (Fᵏx∈Bₖ k x∈B₀)

--------------------------------------------------------------------------
-- If `B 0` is non-empty then it can be shown that the fixed point is in
-- every box `B k`

x*∈B₀ : ∀ {x} → x ∈ᵢ B 0 → x* ∈ᵢ B 0
x*∈B₀ {x} x∈B₀ = begin⟨ x∈B₀ ⟩
  ⇒ x ∈ᵢ B 0            ∴⟨ Fᵏx∈Bₖ k* ⟩
  ⇒ (F ^ k*) x ∈ᵢ B k*  ∴⟨ x∈B[k*]⇒x≈x* ⟩
  ⇒ (F ^ k*) x ≈ x*     ∴⟨ B-cong ◌ (Fᵏx∈B₀ k* x∈B₀) ⟩
  ⇒ x* ∈ᵢ B 0           ∎

x*∈Bₖ : ∀ {x} → x ∈ᵢ B 0 → ∀ k → x* ∈ᵢ B k
x*∈Bₖ x∈B₀ zero    = x*∈B₀ x∈B₀
x*∈Bₖ x∈B₀ (suc k) = begin⟨ x*∈Bₖ x∈B₀ k ⟩
  ⇒ x*   ∈ᵢ B k        ∴⟨ F-mono-B ⟩
  ⇒ F x* ∈ᵢ B (suc k)  ∴⟨ B-cong x*-fixed ⟩
  ⇒ x*   ∈ᵢ B (suc k)  ∎
