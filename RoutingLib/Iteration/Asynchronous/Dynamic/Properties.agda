--------------------------------------------------------------------------------
-- Agda routing library
--
-- Some basic properties of asynchronous iterations
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic.Properties where

open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset; _∉_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Universal; _∈_; _⊆_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Binary.Equality as TableEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed using (IPred; Uᵢ; _∈ᵢ_; _⊆ᵢ_; Universalᵢ)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule

-------------------------------------------------------------------------
-- Basic properties of the asynchronous state function

module _ {a ℓ n} (I : AsyncIterable a ℓ n) (𝓢 : Schedule n) where

  open AsyncIterable I
  open Schedule 𝓢

  -- asyncIter respects equality of times (not immediately obvious due to
  -- the Acc arguments)
  asyncIter-cong : ∀ x₀ {t₁ t₂} (acc₁ : Acc _<_ t₁) (acc₂ : Acc _<_ t₂) →
                   t₁ ≡ t₂ → asyncIter' I 𝓢 x₀ acc₁ ≈ asyncIter' I 𝓢 x₀ acc₂
  asyncIter-cong  x₀ {zero} rec₁ rec₂ refl i with i ∈? ρ 0
  ... | no  _ = ≈ᵢ-refl
  ... | yes _ = ≈ᵢ-refl
  asyncIter-cong x₀ {suc t} (acc rec₁) (acc rec₂) refl i with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no _       | _     | _     = ≈ᵢ-refl
  ... | yes _      | no  _ | _     = ≈ᵢ-refl
  ... | yes _      | yes _ | no  _ = asyncIter-cong x₀ (rec₁ t _) _ refl i
  ... | yes i∈ρ₁₊ₜ | yes _ | yes _ = F-cong (η (suc t)) (ρ (suc t))
    (λ j → asyncIter-cong x₀ (rec₁ (β (suc t) i j) _) _ refl j) i∈ρ₁₊ₜ

  -- If a node is inactive at time t then it has the blank state
  asyncIter-inactive : ∀ x₀ {t} (rec : Acc _<_ t) {i} →
                       i ∉ ρ t → asyncIter' I 𝓢 x₀ rec i ≡ ⊥ i
  asyncIter-inactive x₀ {zero} rec {i} i∉ρ₀ with i ∈? ρ 0
  ... | no  _    = refl
  ... | yes i∈ρ₀ = contradiction i∈ρ₀ i∉ρ₀
  asyncIter-inactive x₀ {suc t} (acc rec) {i} i∉ρ₁₊ₜ with i ∈? ρ (suc t)
  ... | no  _      = refl
  ... | yes i∈ρ₁₊ₜ = contradiction i∈ρ₁₊ₜ i∉ρ₁₊ₜ

-------------------------------------------------------------------------
-- Convergent

module _ {a ℓ n} {I : AsyncIterable a ℓ n} where

  open AsyncIterable I

  partiallyConvergent-shrink : ∀ {p} {X₀ Y₀ : IPred Sᵢ p} → X₀ ⊆ᵢ Y₀ →
                          ∀ {q} {P Q : Pred (Subset n) q} → P ⊆ Q →
                          (Y₀ᶜ : PartiallyConvergent I Y₀ Q) →
                          (∀ e {p} (p∈Q : p ∈ Q) → (PartiallyConvergent.x* Y₀ᶜ e p∈Q) ∈ᵢ X₀) →
                          PartiallyConvergent I X₀ P
  partiallyConvergent-shrink X₀⊆Y₀ P⊆Q Y₀-safe x*∈X₀ = record
    { x*         = λ e p∈P → x* e (P⊆Q p∈P)
    ; k*         = λ e p∈P → k* e (P⊆Q p∈P)
    ; x*-fixed   = λ e p∈P → x*-fixed e (P⊆Q p∈P)
    ; x*-reached = λ x₀∈Y₀ ρ∈Q → x*-reached (X₀⊆Y₀ ∘ x₀∈Y₀) (P⊆Q ∘ ρ∈Q)
    }
    where open PartiallyConvergent Y₀-safe

-------------------------------------------------------------------------
-- Accordant

module _ {a ℓ n} (I : AsyncIterable a ℓ n) where

  open AsyncIterable I

  xy∈Aₚ∧x≈ₚy⇒x≈y : ∀ {p x y} → x ∈ Accordant p → y ∈ Accordant p →
                   x ≈[ p ] y → x ≈ y
  xy∈Aₚ∧x≈ₚy⇒x≈y {p} x∈Aₚ y∈Aₚ x≈ₚy i with i ∈? p
  ... | yes i∈p = x≈ₚy i∈p
  ... | no  i∉p = ≈ᵢ-trans (x∈Aₚ i∉p) (≈ᵢ-sym (y∈Aₚ i∉p))
