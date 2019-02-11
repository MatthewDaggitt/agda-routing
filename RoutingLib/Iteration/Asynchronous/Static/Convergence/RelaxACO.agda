--------------------------------------------------------------------------
-- Uresin & Dubois have a slightly stronger definition of an ACO in that
-- they require that the boxes are nested. In our definition in conditions
-- we only assume that the initial box B₀ is closed with respect to F.
--
-- In this module we show that this is relaxation does not provide any
-- additional power in the sense that for every iteration that obeys our
-- definition of an ACO it is possible to show that it also satisfies
-- Uresin & Dubois's definition. This is proved under the assumption that
-- the initial box B₀ is non-empty. However we would argue that our
-- relaxed definition is easier to work with as the containment can be
-- tricky to prove in practice.
--------------------------------------------------------------------------

open import Data.Product

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.RelaxACO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n} {p} (aco : ACO I∥ p)
  (B₀-nonEmpty : ∃ (_∈ᵢ (ACO.B aco 0)))where

open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Synchronous
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO
  as ACOProperties

open AsyncIterable I∥
open ACO aco
open ACOProperties I∥ aco

--------------------------------------------------------------------------
-- Extract the witness of B₀ being non-empty

x : S
x = proj₁ B₀-nonEmpty

x∈B₀ : x ∈ᵢ B 0
x∈B₀ = proj₂ B₀-nonEmpty

--------------------------------------------------------------------------
-- Define the new boxes

C : ℕ → IPred Sᵢ p
C zero    = B 0
C (suc k) = B (suc k) ∩ C k

--------------------------------------------------------------------------
-- The boxes are nested within one another

Cₖ₊₁⊆Cₖ : ∀ k → C (suc k) ⊆ᵢ C k
Cₖ₊₁⊆Cₖ k {i} x∈Cₖ₊₁ⁱ = proj₂ x∈Cₖ₊₁ⁱ

--------------------------------------------------------------------------
-- All boxes after k* only contain x*

C-finish₁ : ∀ k → x* ∈ᵢ C k
C-finish₁ zero    i = x*∈Bₖ x∈B₀ 0 i
C-finish₁ (suc k) i = (x*∈Bₖ x∈B₀ (suc k) i) , C-finish₁ k i

C-finish₂ : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ C k → x ≈ x*
C-finish₂ {zero}  k*≤k   x∈Cₖ i = k*≤k⇒x∈B[k]⇒x≈x* k*≤k x∈Cₖ i
C-finish₂ {suc k} k*≤1+k x∈Cₖ i = k*≤k⇒x∈B[k]⇒x≈x* k*≤1+k (proj₁ ∘ x∈Cₖ) i

C-finish : ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ᵢ C k) × (∀ {x} → x ∈ᵢ C k → x ≈ x*)
C-finish = k* , x* , λ {k} k*≤k → C-finish₁ k , C-finish₂ k*≤k

--------------------------------------------------------------------------
-- Applying F advances the box number

F-mono-C : ∀ {k x} → x ∈ᵢ C k → F x ∈ᵢ C (suc k)
F-mono-C {zero}  x∈Cₖ i = F-mono-B x∈Cₖ i , F-resp-B₀ x∈Cₖ i
F-mono-C {suc k} x∈Cₖ i = F-mono-B (proj₁ ∘ x∈Cₖ) i , F-mono-C (proj₂ ∘ x∈Cₖ) i
