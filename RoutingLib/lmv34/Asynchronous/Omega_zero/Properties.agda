open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing.Prelude as RoutingPrelude using () renaming (AdjacencyMatrix to AdjacencyMatrix')

module RoutingLib.lmv34.Asynchronous.Omega_zero.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix' algebra n)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (⊤; ⊥)
open import Data.Fin.Subset.Properties using (_∈?_; ∈⊤; ∉⊥)
open import Data.Nat using (zero; suc; _<_; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Function using (const)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous using (IndexedDecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable; asyncIter'; asyncIter)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (ψˢʸⁿᶜ; αˢʸⁿᶜ)
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.lmv34.Asynchronous.Omega_zero algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A
open import RoutingLib.lmv34.Synchronous.Gamma_zero algebra A using (Γ₀)
open import RoutingLib.lmv34.Synchronous.Gamma_zero.Properties algebra A using (Γ₀-cong; ⨁-cong; ⊕ₘ-cong)

open RawRoutingAlgebra algebra using (▷-cong; ≈-refl)
open RoutingPrelude algebra n using (RoutingMatrix; RoutingTable; ≈ₘ-refl; _≈ₜ_; ℝ𝕄ₛ; Decℝ𝕄ₛⁱ) renaming (_≈ₘ_ to infix 4 _≈ₘ_)
open IndexedDecSetoid Decℝ𝕄ₛⁱ using () renaming (isDecEquivalenceᵢ to ℝ𝕄-isDecEquivalenceᵢ)

--------------------------------------------------------------------------------
-- Operation properties

[,]-⊤ : ∀ {X Y : RoutingMatrix} → [ X , Y ] ⊤ ≈ₘ X
[,]-⊤ {X} {Y} i j with i ∈? ⊤
... | no  i∉⊤ = contradiction ∈⊤ i∉⊤
... | yes _   = ≈-refl

[,]-⊥ : ∀ {X Y : RoutingMatrix} → [ X , Y ] ⊥ ≈ₘ Y
[,]-⊥ {X} {Y} i j with i ∈? ⊥
... | no  _   = ≈-refl
... | yes i∈⊥ = contradiction i∈⊥ ∉⊥

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
Γ₀∥ = record
  { Sᵢ   = const RoutingTable
  ; _≈ᵢ_ = _≈ₜ_
  ; F    = Γ₀
  ; isAsyncIterable = record
    { isDecEquivalenceᵢ = ℝ𝕄-isDecEquivalenceᵢ
    ; F-cong = Γ₀-cong
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
  [ Γ₀ X[t] , X[t] ] αˢʸⁿᶜ (suc t) ≡⟨⟩
  [ Γ₀ X[t] , X[t] ] ⊤             ≈⟨ [,]-⊤ ⟩
  Γ₀ X[t]                          ≈⟨ Γ₀-cong (Ω₀ˢʸⁿᶜ=Γ₀' X (rec t ≤-refl)) ⟩
  (Γ₀ ^ (suc t)) X                 ∎
  where open EqReasoning ℝ𝕄ₛ
        X[t] : RoutingMatrix
        X[t] = Ω₀' ψˢʸⁿᶜ X (rec t ≤-refl)

Ω₀ˢʸⁿᶜ=Γ₀ : ∀ X t → Ω₀ ψˢʸⁿᶜ X t ≈ₘ (Γ₀ ^ t) X
Ω₀ˢʸⁿᶜ=Γ₀ X t = Ω₀ˢʸⁿᶜ=Γ₀' X (<-wellFounded t)
