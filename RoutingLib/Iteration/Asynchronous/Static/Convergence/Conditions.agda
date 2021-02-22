--------------------------------------------------------------------------------
-- Agda routing library
--
-- This core module contains the definitions for the pre-conditions for a
-- static asynchronous iteration being convergent. Users interested in using
-- these conditions should not import them from here directly but from
-- `RoutingLib.Iteration.Asynchronous.Static.Convergence` which also exports
-- the associated proofs of convergence.
--------------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Static

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions
  {a ℓ n} (I∥ : AsyncIterable a ℓ n) where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∉_; ⊤)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (tt)
open import Function.Metric.Nat
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary as B
  using (Rel; DecSetoid; _Respects_; Total; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous
  using (IRel; Lift; Decidable; IsIndexedPartialOrder)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Vec.Functional using (max)
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Indexed.Properties

open import RoutingLib.Iteration.Synchronous using (_^_)

open AsyncIterable I∥

--------------------------------------------------------------------------------
-- Asynchronously contracting operator (ACO)
--------------------------------------------------------------------------------
-- Sufficient (and necessary conditions) for convergence as inspired by Üresin
-- and Dubois

record PartialACO {ℓ₁} (X₀ : IPred Sᵢ ℓ₁) ℓ₂ : Set (a ⊔ lsuc ℓ₂ ⊔ ℓ ⊔ ℓ₁) where
  field
    B          : ℕ → IPred Sᵢ ℓ₂

    X₀≋B₀      : X₀ ≋ᵢ B 0
    F-resp-X₀  : ∀ {x} → x ∈ᵢ X₀ → F x ∈ᵢ X₀
    
    Bᵢ-cong    : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
    F-mono-B   : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)

    -- There exists a point k* after which the boxes only contain x*
    x*         : S
    k*         : ℕ
    B-finish   : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*

  B-cong : ∀ {k} → (_∈ᵢ B k) Respects _≈_
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)

ACO : ∀ ℓ₂ → Set (a ⊔ lsuc ℓ₂ ⊔ ℓ)
ACO = PartialACO Uᵢ

partialACO⇒ACO : ∀ {ℓ₁ ℓ₃} {X₀ : IPred Sᵢ ℓ₁} →
                 Universalᵢ X₀ →
                 PartialACO X₀ ℓ₃ → ACO ℓ₃
partialACO⇒ACO _∈X₀ partialACO = record
  { B            = B
  ; Bᵢ-cong      = Bᵢ-cong
  ; X₀≋B₀        = (λ _ → proj₁ X₀≋B₀ (_ ∈X₀)) , _
  ; F-resp-X₀    = _
  ; F-mono-B     = F-mono-B
  ; x*           = x*
  ; k*           = k*
  ; B-finish     = B-finish
  } where open PartialACO partialACO

--------------------------------------------------------------------------------
-- Asynchronously metrically contracting operator (AMCO)
--------------------------------------------------------------------------------
-- Metric conditions that are also sufficient (and necessary) conditions based
-- on those defined by Gurney

record PartialAMCO {p} (X₀ : IPred Sᵢ p) : Set (a ⊔ ℓ ⊔ p) where
  field
    dᵢ                   : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

  d : S → S → ℕ
  d x y = max 0 (λ i → dᵢ (x i) (y i))

  field
    element              : S

    element∈X₀           : element ∈ᵢ X₀
    X₀-closed            : ∀ {x} → x ∈ᵢ X₀ → F x ∈ᵢ X₀
    X₀-cong              : ∀ {i} → (_∈ X₀ i) Respects _≈ᵢ_
    
    dᵢ-isQuasiSemiMetric : ∀ i → IsQuasiSemiMetric {A = Sᵢ i} _≈ᵢ_ dᵢ
    dᵢ-bounded           : ∀ i → Bounded {A = Sᵢ i} dᵢ
    F-strContrOnOrbits   : ∀ {x} → x ∈ᵢ X₀ → F x ≉ x → d (F x) (F (F x)) < d x (F x)
    F-strContrOnFP       : ∀ {x*} → F x* ≈ x* → ∀ {x} → x ∈ᵢ X₀ → x ≉ x* → d x* (F x) < d x* x

  module _ {i} where
    open IsQuasiSemiMetric (dᵢ-isQuasiSemiMetric i) public
      using ()
      renaming
      ( cong to dᵢ-cong
      ; ≈⇒0  to x≈y⇒dᵢ≡0
      ; 0⇒≈  to dᵢ≡0⇒x≈y
      )

AMCO : Set (a ⊔ ℓ)
AMCO = PartialAMCO Uᵢ

partialAMCO⇒AMCO : ∀ {ℓ₁} {X₀ : IPred Sᵢ ℓ₁} →
                   Universalᵢ X₀ →
                   PartialAMCO X₀ → AMCO
partialAMCO⇒AMCO _∈X₀ partialAMCO = record
  { dᵢ                   = dᵢ
  ; element              = element
  ; dᵢ-isQuasiSemiMetric = dᵢ-isQuasiSemiMetric
  ; dᵢ-bounded           = dᵢ-bounded
  ; F-strContrOnOrbits   = λ {x} _ → F-strContrOnOrbits (λ _ → _ ∈X₀)
  ; F-strContrOnFP       = λ {x} Fx*≈x* _ → F-strContrOnFP Fx*≈x* (λ _ → _ ∈X₀)
  } where open PartialAMCO partialAMCO

--------------------------------------------------------------------------------
-- Synchronous conditions --
--------------------------------------------------------------------------------
-- Sufficient but not necessary conditions by Üresin and Dubois
-- It should be noted that these conditions are modified from those proposed by
-- Uresin and Dubois in Proposition 3 in that they require the synchronous fixed
-- point to be unique. The file:
--
--   RoutingLib.Iteration.Asynchronous.Static.Convergence.UresinDubois3Counterexample
--
-- contains a counter-example to Uresin & Dubois' original formulation.

private

  σ : ℕ → S → S
  σ k = (F ^ k)


record PartialSynchronousConditions {p} (X₀ : IPred Sᵢ p) o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

  field
    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

  _≤ₛ_ : Rel S _
  x ≤ₛ y = ∀ i → x i ≤ᵢ y i

  field
    X₀ᵢ-cong          : ∀ {i} → (_∈ X₀ i) Respects _≈ᵢ_
    X₀-closed         : ∀ {x} → x ∈ᵢ X₀ → F x ∈ᵢ X₀
    
    F-monotone        : ∀ {x y} → x ∈ᵢ X₀ → y ∈ᵢ X₀ → x ≤ₛ y → F x ≤ₛ F y
    F-decreasing      : ∀ {x} → x ∈ᵢ X₀ → F x ≤ₛ x
    
    -- σ converges to a unique fixed point
    x*                : S
    x*-fixed          : F x* ≈ x*
    k*                : ℕ
    σ-convergesTo-x*  : ∀ {x} → x ∈ᵢ X₀ → σ k* x ≈ x*
    
  open IsIndexedPartialOrder ≤ᵢ-isPartialOrder public
    renaming
    ( reflexive  to ≤-reflexive
    ; refl       to ≤-refl
    ; trans      to ≤-trans
    ; antisym    to ≤-antisym
    ; reflexiveᵢ to ≤ᵢ-reflexive
    ; reflᵢ      to ≤ᵢ-refl
    ; transᵢ     to ≤ᵢ-trans
    ; antisymᵢ   to ≤ᵢ-antisym
    )

  X₀-cong : (_∈ᵢ X₀) Respects _≈_
  X₀-cong x≈y x∈X₀ i = X₀ᵢ-cong (x≈y i) (x∈X₀ i)


SynchronousConditions : ∀ o → Set (lsuc (a ⊔ ℓ ⊔ o))
SynchronousConditions = PartialSynchronousConditions Uᵢ

partialSync⇒Sync : ∀ {ℓ₁ ℓ₃} {X₀ : IPred Sᵢ ℓ₁} →
                   Universalᵢ X₀ →
                   PartialSynchronousConditions X₀ ℓ₃ →
                   SynchronousConditions ℓ₃
partialSync⇒Sync _∈X₀ pSync = record
  { _≤ᵢ_              = _≤ᵢ_
  ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder
  ; F-monotone        = λ _ _ → F-monotone (λ _ → _ ∈X₀) (λ _ → _ ∈X₀)
  ; F-decreasing      = λ x → F-decreasing (λ i → _ ∈X₀)
  ; x*                = x*
  ; x*-fixed          = x*-fixed
  ; k*                = k*
  ; σ-convergesTo-x*  = λ x → σ-convergesTo-x* (λ i → _ ∈X₀)
  }
  where open PartialSynchronousConditions pSync
