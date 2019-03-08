--------------------------------------------------------------------------------
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
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (tt)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary as B
  using (Rel; DecSetoid; _Respects_; Total; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous
  using (IRel; Lift; Decidable; IsIndexedPartialOrder)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Function.Metric.Nat
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Unary.Indexed.Properties

open import RoutingLib.Iteration.Synchronous using (_^_)

open AsyncIterable I∥

--------------------------------------------------------------------------------
-- Asynchronously contracting operator (ACO)
--------------------------------------------------------------------------------
-- Sufficient (and necessary conditions) for convergence as inspired by Üresin
-- and Dubois

record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
  field
    D             : ℕ → IPred Sᵢ p
    Dᵢ-cong       : ∀ {k i} → (_∈ D k i) Respects _≈ᵢ_
    D₀-universal  : ∀ i x → x ∈ D 0 i
    F-mono-D      : ∀ {k x} → x ∈ᵢ D k → F x ∈ᵢ D (suc k)

    -- There exists a point k* after which the boxes only contain x*
    x*         : S
    k*         : ℕ
    D-finish   : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (D k) x*

  D-cong : ∀ {k} → (_∈ᵢ D k) Respects _≈_
  D-cong x≈y x∈Dₖ i = Dᵢ-cong (x≈y i) (x∈Dₖ i)

record PartialACO {ℓ₁} (X₀ : IPred Sᵢ ℓ₁) ℓ₂ : Set (a ⊔ lsuc ℓ₂ ⊔ ℓ ⊔ ℓ₁) where
  field
    D          : ℕ → IPred Sᵢ ℓ₂

    X₀≋D₀      : X₀ ≋ᵢ D 0
    
    Dᵢ-cong    : ∀ {k i} → (_∈ D k i) Respects _≈ᵢ_
    F-resp-D₀  : ∀ {x} → x ∈ᵢ D 0 → F x ∈ᵢ D 0
    F-mono-D   : ∀ {k x} → x ∈ᵢ D k → F x ∈ᵢ D (suc k)

    -- There exists a point k* after which the boxes only contain x*
    x*         : S
    k*         : ℕ
    D-finish   : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (D k) x*

  D-cong : ∀ {k} → (_∈ᵢ D k) Respects _≈_
  D-cong x≈y x∈Dₖ i = Dᵢ-cong (x≈y i) (x∈Dₖ i)

ACO⇒partialACO : ∀ {ℓ₃} → ACO ℓ₃ → PartialACO Uᵢ ℓ₃
ACO⇒partialACO aco = record
  { D         = D
  ; F-resp-D₀ = λ {x} x∈D₀ → λ i → D₀-universal i (F x i) 
  ; X₀≋D₀     = (λ _ → D₀-universal _ _) , λ _ → tt
  ; Dᵢ-cong   = Dᵢ-cong
  ; F-mono-D  = F-mono-D
  ; x*        = x*
  ; k*        = k*
  ; D-finish  = D-finish
  } where open ACO aco

partialACO⇒ACO : ∀ {ℓ₁ ℓ₃} {X₀ : IPred Sᵢ ℓ₁} →
                 Universalᵢ X₀ →
                 PartialACO X₀ ℓ₃ → ACO ℓ₃
partialACO⇒ACO _∈X₀ pACO = record
  { D            = D
  ; Dᵢ-cong      = Dᵢ-cong
  ; D₀-universal = λ i x → proj₁ X₀≋D₀ (x ∈X₀)
  ; F-mono-D     = F-mono-D
  ; x*           = x*
  ; k*           = k*
  ; D-finish     = D-finish
  } where open PartialACO pACO

partialACO⇒ACO′ : ∀ {ℓ₁} → PartialACO Uᵢ ℓ₁ → ACO ℓ₁
partialACO⇒ACO′ = partialACO⇒ACO (Uᵢ-universal Sᵢ)

--------------------------------------------------------------------------------
-- Asynchronously metrically contracting operator (AMCO)
--------------------------------------------------------------------------------
-- Metric conditions that are also sufficient (and necessary) conditions based
-- on those defined by Gurney

record AMCO : Set (a ⊔ ℓ) where
  field
    dᵢ                   : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

  d : S → S → ℕ
  d x y = max 0 (λ i → dᵢ (x i) (y i))

  field
    element              : S
    dᵢ-isQuasiSemiMetric : ∀ i → IsQuasiSemiMetric {A = Sᵢ i} _≈ᵢ_ dᵢ
    dᵢ-bounded           : ∀ i → Bounded {A = Sᵢ i} dᵢ
    F-strContrOnOrbits   : ∀ {x} → F x ≉ x → d (F x) (F (F x)) < d x (F x)
    F-strContrOnFP       : ∀ {x x*} → F x* ≈ x* → x ≉ x* → d x* (F x) < d x* x

  module _ {i} where
    open IsQuasiSemiMetric (dᵢ-isQuasiSemiMetric i) public
      using ()
      renaming
      ( cong to dᵢ-cong
      ; eq⇒0 to x≈y⇒dᵢ≡0
      ; 0⇒eq to dᵢ≡0⇒x≈y
      )

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
      ; eq⇒0 to x≈y⇒dᵢ≡0
      ; 0⇒eq to dᵢ≡0⇒x≈y
      )

AMCO⇒partialAMCO : AMCO → PartialAMCO Uᵢ
AMCO⇒partialAMCO amco = record
  { dᵢ                   = dᵢ
  ; element              = element
  ; dᵢ-isQuasiSemiMetric = dᵢ-isQuasiSemiMetric
  ; dᵢ-bounded           = dᵢ-bounded
  ; F-strContrOnOrbits   = λ _ → F-strContrOnOrbits
  ; F-strContrOnFP       = λ Fx*≈x* _ → F-strContrOnFP Fx*≈x*
  }
  where open AMCO amco

partialAMCO⇒AMCO : ∀ {ℓ₁} {X₀ : IPred Sᵢ ℓ₁} →
                   Universalᵢ X₀ →
                   PartialAMCO X₀ → AMCO
partialAMCO⇒AMCO _∈X₀ pAMCO = record
  { dᵢ                   = dᵢ
  ; element              = element
  ; dᵢ-isQuasiSemiMetric = dᵢ-isQuasiSemiMetric
  ; dᵢ-bounded           = dᵢ-bounded
  ; F-strContrOnOrbits   = λ {x} → F-strContrOnOrbits (λ i → x i ∈X₀)
  ; F-strContrOnFP       = λ {x} Fx*≈x* → F-strContrOnFP Fx*≈x* (λ i → x i ∈X₀)
  }
  where open PartialAMCO pAMCO

partialAMCO⇒AMCO′ : PartialAMCO Uᵢ → AMCO
partialAMCO⇒AMCO′ = partialAMCO⇒AMCO (Uᵢ-universal Sᵢ)

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

record SynchronousConditions o : Set (lsuc (a ⊔ ℓ ⊔ o)) where

  field
    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

  _≤ₛ_ : Rel S _
  x ≤ₛ y = ∀ i → x i ≤ᵢ y i

  field
    F-monotone        : ∀ {x y} → x ≤ₛ y → F x ≤ₛ F y
    F-decreasing      : ∀ x → F x ≤ₛ x
    
    -- σ converges to a unique fixed point
    x*                : S
    x*-fixed          : F x* ≈ x*
    k*                : ℕ
    σ-convergesTo-x*  : ∀ x → σ k* x ≈ x*
    
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


record PartialSynchronousConditions {p} (D : IPred Sᵢ p) o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

  field
    Dᵢ-cong           : ∀ {i} → (_∈ D i) Respects _≈ᵢ_
    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

  _≤ₛ_ : Rel S _
  x ≤ₛ y = ∀ i → x i ≤ᵢ y i

  field
    D-closed          : ∀ {x} → x ∈ᵢ D → F x ∈ᵢ D
    F-monotone        : ∀ {x y} → x ∈ᵢ D → y ∈ᵢ D → x ≤ₛ y → F x ≤ₛ F y
    F-decreasing      : ∀ {x} → x ∈ᵢ D → F x ≤ₛ x
    
    -- σ converges to a unique fixed point
    x*                : S
    x*-fixed          : F x* ≈ x*
    k*                : ℕ
    σ-convergesTo-x*  : ∀ {x} → x ∈ᵢ D → σ k* x ≈ x*
    
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

  D-cong : (_∈ᵢ D) Respects _≈_
  D-cong x≈y x∈Dₖ i = Dᵢ-cong (x≈y i) (x∈Dₖ i)





sync⇒partialSync : ∀ {ℓ₃} → SynchronousConditions ℓ₃ → PartialSynchronousConditions Uᵢ ℓ₃
sync⇒partialSync sync = record
  { Dᵢ-cong           = λ _ _ → tt
  ; _≤ᵢ_              = _≤ᵢ_
  ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder
  ; D-closed          = λ _ _ → tt
  ; F-monotone        = λ _ _ → F-monotone
  ; F-decreasing      = λ _ → F-decreasing _
  ; x*                = x*
  ; x*-fixed          = x*-fixed
  ; k*                = k*
  ; σ-convergesTo-x*  = λ _ → σ-convergesTo-x* _
  } where open SynchronousConditions sync

partialSync⇒Sync : ∀ {ℓ₁ ℓ₃} {X₀ : IPred Sᵢ ℓ₁} →
                 Universalᵢ X₀ →
                 PartialSynchronousConditions X₀ ℓ₃ →
                 SynchronousConditions ℓ₃
partialSync⇒Sync _∈X₀ pSync = record
  { _≤ᵢ_              = _≤ᵢ_
  ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder
  ; F-monotone        = λ {x} {y} → F-monotone (λ i → x i ∈X₀) (λ i → y i ∈X₀)
  ; F-decreasing      = λ x → F-decreasing (λ i → x i ∈X₀)
  ; x*                = x*
  ; x*-fixed          = x*-fixed
  ; k*                = k*
  ; σ-convergesTo-x*  = λ x → σ-convergesTo-x* (λ i → x i ∈X₀)
  }
  where open PartialSynchronousConditions pSync

partialSync⇒Sync′ : ∀ {ℓ₁} → PartialSynchronousConditions Uᵢ ℓ₁ → SynchronousConditions ℓ₁
partialSync⇒Sync′ = partialSync⇒Sync (Uᵢ-universal Sᵢ)

{-
record FiniteConditions p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where
  open Membership (setoid) using () renaming (_∈_ to _∈L_)

  field
    D₀                : Pred Sᵢ p
    D₀-cong           : ∀ {x y} → x ∈ D₀ → x ≈ y → y ∈ D₀
    D₀-closed         : ∀ {x} → x ∈ D₀ → F x ∈ D₀
    D₀-finite         : ∃ λ xs → ∀ {x} → x ∈ D₀ → x ∈L xs

    -- ξ∈D₀              : ξ ∈ D₀

    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_
    _≟ᵢ_              : Decidable Sᵢ _≈ᵢ_

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

  _≤_ = Lift Sᵢ _≤ᵢ_
  open NonStrictToStrict _≈_ _≤_ using (_<_)

  field
    ξ               : S
    ξ∈D₀            : ξ ∈ D₀
    F-strictlyDecr  : ∀ {x} → x ∈ D₀ → x ≉ ξ → F x < x
    F-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≤ y → F x ≤ F y
    F-cong          : ∀ {x y} → x ≈ y → F x ≈ F y
-}
