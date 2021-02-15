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

open import RoutingLib.Iteration.Asynchronous.Dynamic

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∉_; ⊤) renaming (_∈_ to _∈ₛ_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (tt)
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
open import Function.Metric.Nat
open import Level using (Level; _⊔_) renaming (suc to lsuc)
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

--------------------------------------------------------------------------------
-- Asynchronously contracting operator (ACO) --
--------------------------------------------------------------------------------
-- Sufficient conditions for convergence

module _ {a ℓ n} (𝓘 : AsyncIterable a ℓ n) where
  open AsyncIterable 𝓘

  record ACO ℓ₃ : Set (a ⊔ ℓ ⊔ lsuc ℓ₃) where
    field
      B            : Epoch → Subset n → ℕ → IPred Sᵢ ℓ₃
      Bᵢ-cong      : ∀ {e p k i} → (_∈ B e p k i) Respects _≈ᵢ_
      B₀-universal : ∀ e p i x → x ∈ B e p 0 i
      B-finish     : ∀ e p → ∃₂ λ k* x* → ∀ {k} → k* ≤ k →
                       (x* ∈ᵢ B e p k × (∀ {x} → x ∈ᵢ B e p k → x ≈ x*))
      B-null       : ∀ {e p k i} → i ∉ p → ⊥ i ∈ B e p k i
      F-mono-B     : ∀ {e p k x} → x ∈ Accordant p → x ∈ᵢ B e p k → F e p x ∈ᵢ B e p (suc k)

  record PartialACO {ℓ₁ ℓ₂}
                    (B₀ : IPred Sᵢ ℓ₁)          -- Set of allowable initial states
                    (Q  : Pred (Subset n) ℓ₂)   -- Set of allowable sets of participants
                    ℓ₃ : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃ ⊔ ℓ) where
    field
      B         : Epoch → {p : Subset n} → .(p ∈ Q) → ℕ → IPred Sᵢ ℓ₃
      B₀-cong   : (_∈ᵢ B₀) Respects _≈_
      B₀-eqᵢ     : ∀ {e p} .(p∈Q : p ∈ Q) → B₀ ≋ᵢ B e p∈Q 0
      Bᵢ-cong    : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {k i} → (_∈ B e p∈Q k i) Respects _≈ᵢ_
      B-finish   : ∀ e {p} .(p∈Q : p ∈ Q) → ∃₂ λ k* x* → ∀ {k} → k* ≤ k →
                     (x* ∈ᵢ B e p∈Q k × (∀ {x} → x ∈ᵢ B e p∈Q k → x ≈ x*))
      B-null     : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {k i} → i ∉ p → ⊥ i ∈ B e p∈Q k i
      F-mono-B   : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {k x} → x ∈ Accordant p →
                   x ∈ᵢ B e p∈Q k → F e p x ∈ᵢ B e p∈Q (suc k)
      F-resp-B₀  : ∀ {e p} → .(p ∈ Q) → ∀ {x} → x ∈ᵢ B₀ → F e p x ∈ᵢ B₀

  -- Converting between partial and non-partial forms

  ACO⇒partialACO : ∀ {ℓ₃} → ACO ℓ₃ → PartialACO Uᵢ U ℓ₃
  ACO⇒partialACO aco = record
    { B₀-cong   = λ _ _ _ → tt
    ; F-resp-B₀ = λ _ _ _ → tt
    ; B         = λ e {p} _ → B e p
    ; B₀-eqᵢ    = λ _ → (λ _ → B₀-universal _ _ _ _) , (λ _ → tt)
    ; Bᵢ-cong   = λ _ → Bᵢ-cong
    ; B-finish  = λ e {p} _ → B-finish e p
    ; B-null    = λ _ → B-null
    ; F-mono-B  = λ _ → F-mono-B
    } where open ACO aco

  partialACO⇒ACO : ∀ {ℓ₁ ℓ₂ ℓ₃} {B₀ : IPred Sᵢ ℓ₁} {Q : Pred (Subset n) ℓ₂} →
                   Universalᵢ B₀ → Universal Q →
                   PartialACO B₀ Q ℓ₃ → ACO ℓ₃
  partialACO⇒ACO _∈B₀ _∈Q pACO = record
    { B            = λ e p → B e (p ∈Q)
    ; Bᵢ-cong      = Bᵢ-cong (_ ∈Q)
    ; B₀-universal = λ e p x i → proj₁ (B₀-eqᵢ (_ ∈Q)) (_ ∈B₀)
    ; B-finish     = λ e p → B-finish e (p ∈Q)
    ; B-null       = B-null (_ ∈Q)
    ; F-mono-B     = F-mono-B (_ ∈Q)
    } where open PartialACO pACO

  partialACO⇒ACO′ : ∀ {ℓ₁} → PartialACO Uᵢ U ℓ₁ → ACO ℓ₁
  partialACO⇒ACO′ = partialACO⇒ACO (Uᵢ-universal Sᵢ) U-Universal

--------------------------------------------------------------------------------
-- Asynchronously Metrically Contracting Operator (AMCO)
--------------------------------------------------------------------------------
-- Sufficient conditions for convergence

module _ {a ℓ n} (𝓘 : AsyncIterable a ℓ n) where
  open AsyncIterable 𝓘
  
  record AMCO : Set (a ⊔ ℓ) where
    field
      dᵢ                   : Epoch → Subset n → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
      dᵢ-isQuasiSemiMetric : ∀ e p i → IsQuasiSemiMetric _≈ᵢ_ (dᵢ e p {i})
      dᵢ-bounded           : ∀ e p → ∃ λ dₘₐₓ → ∀ {i} x y → dᵢ e p {i} x y ≤ dₘₐₓ

    dₛᵢ : Epoch → Subset n → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
    dₛᵢ e p {i} x y = if ⌊ i ∈? p ⌋ then dᵢ e p x y else 0

    d : Epoch → Subset n → S → S → ℕ
    d e p x y = max 0 (λ i → dₛᵢ e p (x i) (y i))

    field
      F-strContrOnOrbits  : ∀ {e p x} → x ∈ Accordant p → F e p x ≉[ p ] x → d e p (F e p x) (F e p (F e p x)) < d e p x (F e p x)
      F-strContrOnFP      : ∀ {e p x} → x ∈ Accordant p → ∀ {x*} → F e p x* ≈ x* → x ≉[ p ] x* → d e p x* (F e p x) < d e p x* x
      F-pres-Aₚ           : ∀ {e p x} → x ∈ Accordant p → F e p x ∈ Accordant p

    module _ e p {i} where
      open IsQuasiSemiMetric (dᵢ-isQuasiSemiMetric e p i) public
        using ()
        renaming
        ( cong to dᵢ-cong
        ; ≈⇒0  to x≈y⇒dᵢ≡0
        ; 0⇒≈  to dᵢ≡0⇒x≈y
        )


  record PartialAMCO {q} (Q : Pred (Subset n) q) : Set (a ⊔ ℓ ⊔ q) where
    field
      dᵢ                   : Epoch → {p : Subset n} → .(p ∈ Q) → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
      dᵢ-isQuasiSemiMetric : ∀ e {p} .(p∈Q : p ∈ Q) i → IsQuasiSemiMetric _≈ᵢ_ (dᵢ e p∈Q {i})
      dᵢ-bounded           : ∀ e {p} .(p∈Q : p ∈ Q) → ∃ λ dₘₐₓ → ∀ {i} x y → dᵢ e p∈Q {i} x y ≤ dₘₐₓ

    dₛᵢ : Epoch → {p : Subset n} → .(p ∈ Q) → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
    dₛᵢ e {p} p∈Q {i} x y = if ⌊ i ∈? p ⌋ then dᵢ e p∈Q x y else 0

    d : Epoch → {p : Subset n} → .(p ∈ Q) → S → S → ℕ
    d e p∈Q x y = max 0 (λ i → dₛᵢ e p∈Q (x i) (y i))

    field
      F-strContrOnOrbits  : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {x} → x ∈ Accordant p → F e p x ≉[ p ] x → d e p∈Q (F e p x) (F e p (F e p x)) < d e p∈Q x (F e p x)
      F-strContrOnFP      : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {x} → x ∈ Accordant p → ∀ {x*} → F e p x* ≈ x* → x ≉[ p ] x* → d e p∈Q x* (F e p x) < d e p∈Q x* x
      F-pres-Aₚ           : ∀ {e p} .(p∈Q : p ∈ Q) → ∀ {x} → x ∈ Accordant p → F e p x ∈ Accordant p

    module _ e {p} .(p∈Q : p ∈ Q) {i} where
      open IsQuasiSemiMetric (dᵢ-isQuasiSemiMetric e p∈Q i) public
        using ()
        renaming
        ( cong to dᵢ-cong
        ; ≈⇒0  to x≈y⇒dᵢ≡0
        ; 0⇒≈  to dᵢ≡0⇒x≈y
        )

  AMCO⇒partialAMCO : AMCO → PartialAMCO U
  AMCO⇒partialAMCO amco = record
    { dᵢ                   = λ e {p} _ → dᵢ e p
    ; dᵢ-isQuasiSemiMetric = λ e {p} _ → dᵢ-isQuasiSemiMetric e p
    ; dᵢ-bounded           = λ e {p} _ → dᵢ-bounded e p
    ; F-strContrOnOrbits   = λ _ → F-strContrOnOrbits
    ; F-strContrOnFP       = λ _ → F-strContrOnFP
    ; F-pres-Aₚ            = λ _ → F-pres-Aₚ
    } where open AMCO amco

  partialAMCO⇒AMCO : ∀ {ℓ₁} {Q : Pred (Subset n) ℓ₁} → Universal Q →
                    PartialAMCO Q → AMCO
  partialAMCO⇒AMCO _∈Q partialAMCO = record
    { dᵢ                   = λ e p → dᵢ e (p ∈Q)
    ; dᵢ-isQuasiSemiMetric = λ e p → dᵢ-isQuasiSemiMetric e (p ∈Q)
    ; dᵢ-bounded           = λ e p → dᵢ-bounded e (p ∈Q)
    ; F-strContrOnOrbits   = F-strContrOnOrbits (_ ∈Q)
    ; F-strContrOnFP       = F-strContrOnFP (_ ∈Q)
    ; F-pres-Aₚ            = F-pres-Aₚ (_ ∈Q)
    } where open PartialAMCO partialAMCO

  partialAMCO⇒AMCO′ : PartialAMCO U → AMCO
  partialAMCO⇒AMCO′ = partialAMCO⇒AMCO U-Universal
