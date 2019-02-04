open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⊤) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product as Prod using (∃; ∃₂; proj₂; proj₁; _,_; _×_; map)
open import Function using (id; _∘_; _$_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using (_⊔_)
open import Relation.Binary using (tri<; tri≈; tri>; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _⊆_) renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Properties
open import RoutingLib.Function
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (asyncIter-cong; asyncIter-inactive)
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO as ACOProperties
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod


module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.IncompleteProofs.ConvergentImpliesACO
  {a ℓ n} (I : AsyncIterable a ℓ n) (convergent : Convergent I) where

open AsyncIterable I

module _ (x₀ : S) where

{-
  P : (sc : Schedule n) → Epoch → Subset n → ℕ → IPred Sᵢ ℓ

  Pᵢ-cong : ∀ {s e p k i} → (_∈ᵤ P s e p k i) Respects _≈ᵢ_






  B : Epoch → Subset n → ℕ → IPred Sᵢ ℓ
  B e p k i x = ∃ λ s → x ∈ᵤ P s e p k i

  B₀-eqᵢ : ∀ {e p} f q {i} {xᵢ} →
           xᵢ ∈ᵤ B e p 0 i → xᵢ ∈ᵤ B f q 0 i
  B₀-eqᵢ f q = {!!}

  Bᵢ-cong : ∀ {e p k i} → (_∈ᵤ B e p k i) Respects _≈ᵢ_
  Bᵢ-cong x≈y (s , x∈Pₛₑₚₖᵢ) = s , Pᵢ-cong x≈y x∈Pₛₑₚₖᵢ



  B-finish : ∀ e p → ∃₂ λ k* x* →
             ∀ {k} → k* ≤ k → (x* ∈ B e p k) × (∀ {x} → x ∈ B e p k → x ≈ x*)
  B-finish e p = {!!}

  B-null : ∀ {e p k i} → i ∉ₛ p → ⊥ i ∈ᵤ B e p k i
  B-null i∉p = {!!} , {!!}

  F-resp-B₀ : ∀ {e p} {x} → x ∈ B e p 0 → F e p x ∈ B e p 0
  F-resp-B₀ x∈Bₑₚ₀ i = {!!} , {!!}


  B-sim-P : ∀ e p → ∃ λ (s : Schedule n) → ∀ k → B e p k ≋ᵢ P s e p k
  B-sim-P = {!!}

  P-carry : ∀ {s₁ e p x k} i → x ∈ P s₁ e p k → ∃ λ s₂ →
              (P s₁ e p k ≋ᵢ P s₂ e p k) ×
              ∃ λ t → F e p x i ≈ᵢ asyncIter I s₁ x₀ t i
  P-carry = {!!}

  -- B-sim-P₂ : ∀ e p →

  F-mono-B : ∀ {e p k x} → WellFormed p x → x ∈ B e p k → F e p x ∈ B e p (suc k)
  F-mono-B {e} {p} {k} {x} x∈Aₚ x∈Bₑₚₖ i with B-sim-P e p
  ...   | (s₁ , Bₑₚ≋Pₛ₁ₑₚ) with P-carry {s₁} {e} {p} {x} {k} i {!!}
  ...     | (s₂ ,  Pₛ₁ₑₚₖ≋Pₛ₂ₑₚₖ , (t , Fxᵢ≈δᵗᵢ)) = s₂ , (begin⟨ {!!} ⟩
    ⇒ asyncIter I s₁ x₀ t i ∈ᵤ P s₂ e p (suc k) i ∴⟨ {!!} ⟩
    ⇒ F e p x i             ∈ᵤ P s₂ e p (suc k) i ∎)

  aco : ACO I ℓ
  aco = record
    { B         = B
    ; B₀-eqᵢ    = B₀-eqᵢ
    ; Bᵢ-cong   = Bᵢ-cong
    ; B-finish  = B-finish
    ; B-null    = B-null
    ; F-resp-B₀ = F-resp-B₀
    ; F-mono-B  = F-mono-B
    }
-}
