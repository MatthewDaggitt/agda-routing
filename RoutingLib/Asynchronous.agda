open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Nat using (ℕ; _<_; _≤_; _+_; s≤s; zero; suc)
open import Data.Nat.Properties using (1+n≰n; m≤m+n; n≤m+n)
open import Data.Bool using (Bool)
open import Data.Product using (∃; _×_; proj₂; _,_)
open import Relation.Binary using (_⇒_; Reflexive; Symmetric; Transitive; IsEquivalence; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬∀⟶∃¬; contradiction)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Data.Nat.Properties using (≤-refl)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕤-sync)

module RoutingLib.Asynchronous where

  open Schedule

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed and carried out on n separate processors 
  record Parallelisation a ℓ (n : ℕ) : Set (lsuc (a ⊔ ℓ)) where
    field
      -- The type of information at each processor
      Sᵢ : Fin n → Setoid a ℓ
      -- The update functions: "σ X i" is the result of processor i activating on state X 
      σ : (∀ j → Setoid.Carrier (Sᵢ j)) → ∀ i → Setoid.Carrier (Sᵢ i)

    -- Re-export setoid properties with the associated processor left implicit
    module _ {i} where
      open Setoid (Sᵢ i)
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
    M = (∀ i → Mᵢ {i})

    _≈ₘ_ : Rel M ℓ
    X ≈ₘ Y = ∀ i → X i ≈ᵢ Y i

    _≉ₘ_ : Rel M ℓ
    X ≉ₘ Y = ¬ (X ≈ₘ Y)


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
  record IsAsynchronouslySafe {a ℓ n} (p : Parallelisation a ℓ n) : Set (lsuc (a ⊔ ℓ)) where
    open Parallelisation p
    field
      m*         : M
      m*-reached : ∀ 𝕤 X → ∃ λ tᶜ → ∀ t → δ 𝕤 (tᶜ + t) X ≈ₘ m*

