--------------------------------------------------------------------------------
-- Agda routing library
--
-- This core module contains the definitions for the pre-conditions for a
-- dynamic asynchronous iteration being convergent.
--------------------------------------------------------------------------------

-- Note these conditions should not be imported from here directly but from
-- `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence` which also exports
-- the associated proofs of convergence.

-- Each of the conditions comes in two forms `X` and `PartialX`, e.g. `ACO` and
-- `PartialACO`. The `X` forms guarantee convergence from any initial state for
-- any schedule. The `PartialX` forms only guarantee convergence from a subset
-- of initial states and schedules. The sets of valid initial states and
-- schedules are passed as parameters to the `PartialX` records.

-- Note that the `X` forms are not defined in terms of the `PartialX` forms
-- parameterised by the entire state space and all possible schedules, in order
-- to avoid users of the `X` forms having to provide extraneous proofs that the
-- states and schedules are members of these universal sets.

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∉_; ⊤) renaming (_∈_ to _∈ₛ_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (tt)
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
open import Function.Metric.Nat
open import Level using (Level; 0ℓ; _⊔_) renaming (suc to lsuc)
open import Level.Literals using (#_)
open import Relation.Binary as B using (DecSetoid; _Respects_; Total; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Universal; U; _∈_)
open import Relation.Unary.Properties using (U-Universal)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Vec.Functional using (max)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid_at_)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEq
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Indexed.Properties

open import RoutingLib.Iteration.Asynchronous.Dynamic

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
  {a ℓ n} (𝓘 : AsyncIterable a ℓ n) where
open AsyncIterable 𝓘

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

--------------------------------------------------------------------------------
-- Initial set
--------------------------------------------------------------------------------

record IsValidInitialSet (X : IPred Sᵢ ℓ₁) : Set (a ⊔ ℓ₁) where
  field
    -- The set it closed over every operator
    F-pres-X  : ∀ {e p x} → x ∈ᵢ X → F e p x ∈ᵢ X
    -- The set contains the non-participating set
    ⊥∈X       : ⊥ ∈ᵢ X

-- The universal set is a valid initial set
Uᵢ-validInitialSet : IsValidInitialSet Uᵢ
Uᵢ-validInitialSet = _
  
--------------------------------------------------------------------------------
-- Asynchronously contracting operator (ACO) --
--------------------------------------------------------------------------------
-- Sufficient conditions for convergence

record LocalACO (X : IPred Sᵢ ℓ₁) (e : Epoch) (p : Subset n) ℓ₃
                : Set (a ⊔ ℓ ⊔ ℓ₁ ⊔ lsuc ℓ₃) where

  F′ : S → S
  F′ = F e p
  
  field
    B         : ℕ → IPred Sᵢ ℓ₃
    Bᵢ-cong   : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
    X⊆B₀      : X ⊆ᵢ B 0
    B-null    : ∀ {k i} → i ∉ p → ⊥ i ∈ B k i
    F-mono-B  : ∀ {k x} → x ∈ᵢ X → x ∈ Accordant p → x ∈ᵢ B k → F′ x ∈ᵢ B (suc k)
    B-finish  : ∃₂ λ k* x* → x* ∈ᵢ X × (∀ {k} → k ≥ k* →
                     (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≈ x*)))

PartialACO : ∀ (X : IPred Sᵢ ℓ₁) (C : Pred (Epoch × Subset n) ℓ₂) ℓ₃ → Set (a ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
PartialACO X C ℓ₃ = ∀ {e p} .(ep∈C : (e , p) ∈ C) → LocalACO X e p ℓ₃

ACO : ∀ ℓ₃ → Set (a ⊔ ℓ ⊔ lsuc ℓ₃)
ACO = PartialACO Uᵢ U


--------------------------------------------------------------------------------
-- Asynchronously Metrically Contracting Operator (AMCO)
--------------------------------------------------------------------------------
-- Sufficient conditions for convergence

record LocalAMCO {ℓ₁} (X : IPred Sᵢ ℓ₁)
                 (e : Epoch) (p : Subset n)
                 : Set (a ⊔ ℓ ⊔ ℓ₁) where
  field
    dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

  dₛᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ
  dₛᵢ {i} x y = if ⌊ i ∈? p ⌋ then dᵢ x y else 0

  d : S → S → ℕ
  d x y = max 0 (λ i → dₛᵢ (x i) (y i))

  F′ : S → S
  F′ = F e p
  
  field
    dᵢ-isQuasiSemiMetric : ∀ i → IsQuasiSemiMetric {A = Sᵢ i} _≈ᵢ_ dᵢ
    dᵢ-bounded           : ∃ λ dₘₐₓ → ∀ {i} x y → dᵢ {i} x y ≤ dₘₐₓ
    F-strContrOnOrbits   : ∀ {x} → x ∈ᵢ X → x ∈ Accordant p → F′ x ≉[ p ] x → d (F′ x) (F′ (F′ x)) < d x (F′ x)
    F-strContrOnFP       : ∀ {x} → x ∈ᵢ X → x ∈ Accordant p → ∀ {x*} → F′ x* ≈ x* → x ≉[ p ] x* → d x* (F′ x) < d x* x
    F-pres-Aₚ            : ∀ {x} → x ∈ᵢ X → x ∈ Accordant p → F′ x ∈ Accordant p

  module _ {i} where
    open IsQuasiSemiMetric (dᵢ-isQuasiSemiMetric i) public
      using ()
      renaming
      ( cong to dᵢ-cong
      ; ≈⇒0  to x≈y⇒dᵢ≡0
      ; 0⇒≈  to dᵢ≡0⇒x≈y
      )

PartialAMCO : (X : IPred Sᵢ ℓ₁) (C : Pred (Epoch × Subset n) ℓ₂) → Set (a ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂)
PartialAMCO X C = ∀ {e p} → .((e , p) ∈ C) → LocalAMCO X e p

AMCO : Set (a ⊔ ℓ)
AMCO = PartialAMCO Uᵢ U
