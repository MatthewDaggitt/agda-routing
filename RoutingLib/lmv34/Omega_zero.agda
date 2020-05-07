open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Omega_zero
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤; ⊥)
open import Data.Fin.Subset.Properties using (_∈?_; ∈⊤; ∉⊥)
open import Data.Nat using (zero; suc; s≤s; _<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Function using (const)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.lmv34.Gamma_zero algebra A using (Γ₀)
open import RoutingLib.lmv34.Gamma_zero.Algebra algebra n using (_⊕ₘ_; ⨁)
open import RoutingLib.lmv34.Gamma_zero.Properties algebra A using (Γ₀-cong; ⨁-cong; ⊕ₘ-cong)
open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter; asyncIter')
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; αˢʸⁿᶜ; βˢʸⁿᶜ; βˢʸⁿᶜ-causality)
open import RoutingLib.Iteration.Synchronous using (_^_)

open RawRoutingAlgebra algebra using (Route; _▷_; ▷-cong)
open Routing algebra n using (RoutingTable; RoutingMatrix; AdjacencyMatrix; ℝ𝕄ₛ; Decℝ𝕄ₛⁱ; ≈ₘ-refl; _≈ₜ_; I) renaming (_≈ₘ_ to infix 4 _≈ₘ_)
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

-- Asynchronous (generalised) adjancency matrix application
_❪_❫ : AdjacencyMatrix → (Fin n → Fin n → Fin n → Route) → RoutingMatrix
(A ❪ f ❫) i j = ⨁ (λ k → (A i k) ▷ (f i k j))

-- Asynchronous (generalised) version of the Γ₀ operator
Γ₀' : (Fin n → RoutingMatrix) → RoutingMatrix
Γ₀' X = A ❪ X ❫ ⊕ₘ I

--------------------------------------------------------------------------------
-- Implementation of Ω₀

-- We first define Ω₀ with an explicit accessible argument.
-- This is required to prove guaranteed termination.

module _ (ψ : Schedule n) where
  open Schedule ψ

  Ω₀' : RoutingMatrix → {t : 𝕋} → Acc _<_ t → RoutingMatrix
  Ω₀' X {zero}  _         = X
  Ω₀' X {suc t} (acc rec) = [ Γ₀' X[β[t+1]] , X[t] ] α (suc t)
    where X[t] : RoutingMatrix
          X[t] = Ω₀' X (rec t ≤-refl)
          X[β[t+1]] : Fin n → RoutingMatrix
          X[β[t+1]] i q j = Ω₀' X (rec (β (suc t) i q) (s≤s (β-causality t i q))) q j

Ω₀ : Schedule n → RoutingMatrix → 𝕋 → RoutingMatrix
Ω₀ ψ X t = Ω₀' ψ X (<-wellFounded t)

--------------------------------------------------------------------------------
-- Operation properties

postulate
  [,]-⊤ : ∀ {A : Fin n → Set a} → ∀ {X Y : Vectorᵢ A} → [ X , Y ] ⊤ ≡ X
  [,]-⊥ : ∀ {A : Fin n → Set a} → ∀ {X Y : Vectorᵢ A} → [ X , Y ] ⊥ ≡ Y

[,]-⊤ᵢ : ∀ {A : Fin n → Set a} → ∀ {X Y : Vectorᵢ A} → ∀ i → ([ X , Y ] ⊤) i ≡ X i
[,]-⊤ᵢ {A} {X} {Y} i with i ∈? ⊤
... | no  i∉⊤ = contradiction ∈⊤ i∉⊤
... | yes _   = refl

[,]-⊥ᵢ : ∀ {A : Fin n → Set a} → ∀ {X Y : Vectorᵢ A} → ∀ i → ([ X , Y ] ⊥) i ≡ Y i
[,]-⊥ᵢ {A} {X} {Y} i with i ∈? ⊥
... | no  _   = refl
... | yes i∈⊥ = contradiction i∈⊥ ∉⊥

❪❫-cong : ∀ {X X'} → (∀ i → X i ≈ₘ X' i) → A ❪ X ❫ ≈ₘ A ❪ X' ❫
❪❫-cong X=X' i j = ⨁-cong (λ {k} → ▷-cong (A i k) (X=X' i k j))

Γ₀'-cong : ∀ {X X'} → (∀ i → X i ≈ₘ X' i) → Γ₀' X ≈ₘ Γ₀' X'
Γ₀'-cong X=X' = ⊕ₘ-cong (❪❫-cong X=X') ≈ₘ-refl

--------------------------------------------------------------------------------
-- Proof that Ω₀ is equivalent to a definition using asyncIter

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

module _ (ψ : Schedule n) where
  open Schedule ψ

  Ω₀'-asyncIter' : ∀ X {t} (accₜ : Acc _<_ t) → Ω₀' ψ X accₜ ≈ₘ (asyncIter' Γ₀∥) ψ X accₜ
  Ω₀'-asyncIter' X {zero}  _         = ≈ₘ-refl
  Ω₀'-asyncIter' X {suc t} (acc rec) i with i ∈? α (suc t)
  ... | no  _ = Ω₀'-asyncIter' X (rec t ≤-refl) i
  ... | yes _ = Γ₀'-cong (λ i q j → Ω₀'-asyncIter' X (rec (β (suc t) i q) (s≤s (β-causality t i q))) q j) i
  
Ω₀-asyncIter : ∀ ψ X t → Ω₀ ψ X t ≈ₘ (asyncIter Γ₀∥) ψ X t
Ω₀-asyncIter ψ X t = Ω₀'-asyncIter' ψ X (<-wellFounded t)

--------------------------------------------------------------------------------
-- Proof that Γ₀ is indeed the synchronous version of Ω₀

Ω₀ˢʸⁿᶜ=Γ₀' : ∀ X {t} (accₜ : Acc _<_ t) → Ω₀' ψˢʸⁿᶜ X accₜ ≈ₘ (Γ₀ ^ t) X
Ω₀ˢʸⁿᶜ=Γ₀' X {zero}  _         = ≈ₘ-refl
Ω₀ˢʸⁿᶜ=Γ₀' X {suc t} (acc rec) = begin
  Ω₀' ψˢʸⁿᶜ X (acc rec)            ≡⟨⟩
  [ Γ₀ X[t] , X[t] ] αˢʸⁿᶜ (suc t) ≡⟨ [,]-⊤ ⟩
  Γ₀ X[t]                          ≈⟨ Γ₀-cong (Ω₀ˢʸⁿᶜ=Γ₀' X (rec t ≤-refl)) ⟩
  (Γ₀ ^ (suc t)) X                 ∎
  where open EqReasoning ℝ𝕄ₛ
        X[t] : RoutingMatrix
        X[t] = Ω₀' ψˢʸⁿᶜ X (rec t ≤-refl)

Ω₀ˢʸⁿᶜ=Γ₀ : ∀ X t → Ω₀ ψˢʸⁿᶜ X t ≈ₘ (Γ₀ ^ t) X
Ω₀ˢʸⁿᶜ=Γ₀ X t = Ω₀ˢʸⁿᶜ=Γ₀' X (<-wellFounded t)
