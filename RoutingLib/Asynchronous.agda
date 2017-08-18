open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; _<_; _≤_; _+_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃)
open import Relation.Binary using (DecSetoid; Setoid; Rel; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕤-sync)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality

module RoutingLib.Asynchronous where

  open Schedule

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed and carried out on n separate processors 
  record Parallelisation {a ℓ} (S : Setoid a ℓ) (n : ℕ) : Set (lsuc (a ⊔ ℓ)) where

    open Setoid S
      renaming 
      ( Carrier   to Mᵢ
      ; _≈_       to _≈ᵢ_
      ; reflexive to ≈ᵢ-reflexive
      ; refl      to ≈ᵢ-refl
      ; sym       to ≈ᵢ-sym
      ; trans     to ≈ᵢ-trans
      ) public
        
    -- The global state space
    M : Set a
    M = Table Mᵢ n

    open TableEquality S renaming (_≈ₜ_ to _≈ₘ_; _≉ₜ_ to _≉ₘ_) public

    field
      -- The update functions: "σ X i" is the result of processor i activating on state X 
      σ      : M → M
      σ-cong : σ Preserves _≈ₘ_ ⟶ _≈ₘ_

    -- The asynchronous state function
    δ' : Schedule n → ∀ {t} → Acc _<_ t → M → M
    δ' 𝕤 {zero}  _           X = X
    δ' 𝕤 {suc t} (acc tAcc) X i with i ∈? α 𝕤 (suc t)
    ... | no  i∉αₜ = δ' 𝕤 (tAcc t ≤-refl) X i
    ... | yes i∈αₜ = σ (λ k → δ' 𝕤 (tAcc (β 𝕤 (suc t) i k) (causal 𝕤 t i k)) X k) i

    δ : Schedule n → ℕ → M → M
    δ 𝕤 t = δ' 𝕤 (<-wf t)

    -- The synchronous state function
    σ^ : ℕ → M → M
    σ^ = δ (𝕤-sync n)


  -----------
  -- Other --
  -----------
  
  -- A record encapsulating the idea that p is a well behaved parallelisation
  record IsAsynchronouslySafe {a ℓ n} {S : Setoid a ℓ} (p : Parallelisation S n) : Set (lsuc (a ⊔ ℓ)) where
  
    open Parallelisation p
    
    field
      m*         : M
      m*-reached : ∀ 𝕤 X → ∃ λ tᶜ → ∀ t → δ 𝕤 (tᶜ + t) X ≈ₘ m*
