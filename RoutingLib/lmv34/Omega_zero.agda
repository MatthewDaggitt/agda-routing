open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)

module RoutingLib.lmv34.Omega_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤; ⊥)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using (Acc; <-wellFounded)
open import Function using (const)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.lmv34.Gamma_zero algebra A using (Γ₀)
open import RoutingLib.lmv34.Gamma_zero.Properties algebra A using (Γ₀-cong)
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; ψˢʸⁿᶜ-isSynchronous)
open import RoutingLib.Iteration.Synchronous using (_^_)

open Routing algebra n using (RoutingTable; RoutingMatrix; Decℝ𝕄ₛⁱ; _≈ₘ_; _≈ₜ_)
open IndexedDecSetoid Decℝ𝕄ₛⁱ using () renaming (isDecEquivalenceᵢ to ℝ𝕄-isDecEquivalenceᵢ)

--------------------------------------------------------------------------------
-- Algebra

-- Generalised Vector (maybe already implemented?)
Vectorᵢ : (Fin n → Set a) → Set a
Vectorᵢ Aᵢ = (i : Fin n) → Aᵢ i

-- Choice operator
infix 5 [_,_]_
[_,_]_ : ∀ {A : Fin n → Set a} → Vectorᵢ A → Vectorᵢ A → Subset n → Vectorᵢ A
([ X , Y ] S) i with (i ∈? S)
... | yes _ = X i
... | no  _ = Y i

--------------------------------------------------------------------------------
-- Definition

Γ₀∥ : AsyncIterable a ℓ n
Γ₀∥ = record {
  Sᵢ   = const RoutingTable;
  _≈ᵢ_ = _≈ₜ_;
  F    = Γ₀;
  isAsyncIterable = record {
    isDecEquivalenceᵢ = ℝ𝕄-isDecEquivalenceᵢ;
    F-cong = Γ₀-cong
    }
  }

-- We first define Ω₀ with an explicit accessible argument.
-- This allows for recursive reasoning about the function.
Ω₀' : Schedule n → RoutingMatrix → {t : 𝕋} → Acc _<_ t → RoutingMatrix
Ω₀' = asyncIter' Γ₀∥

Ω₀ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
Ω₀ ψ X t = Ω₀' ψ X (<-wellFounded t)

--------------------------------------------------------------------------------
-- Properties

-- Operators
postulate
  [,]-⊤ : ∀ {A : Fin n → Set a} → ∀ (X Y : Vectorᵢ A) → ([ X , Y ] ⊤) ≡ X
  [,]-⊥ : ∀ {A : Fin n → Set a} → ∀ (X Y : Vectorᵢ A) → ([ X , Y ] ⊥) ≡ Y

-- Γ₀ is indeed the synchronous version of Ω₀
Ω₀ˢʸⁿᶜ=Γ₀ : ∀ X t → Ω₀ ψˢʸⁿᶜ X t ≈ₘ (Γ₀ ^ t) X
Ω₀ˢʸⁿᶜ=Γ₀ = ψˢʸⁿᶜ-isSynchronous Γ₀∥
