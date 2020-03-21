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
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary as B
  using (Rel; DecSetoid; _Respects_; Total; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous
  using (IRel; Lift; Decidable; IsIndexedPartialOrder)
open import Relation.Unary using (_∈_)

open import RoutingLib.Data.Vec.Functional using (max)
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
    B             : ℕ → IPred Sᵢ p
    Bᵢ-cong       : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
    B₀-universal  : ∀ i x → x ∈ B 0 i
    F-mono-B      : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)

    -- There exists a point k* after which the boxes only contain x*
    x*         : S
    k*         : ℕ
    B-finish   : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*

  B-cong : ∀ {k} → (_∈ᵢ B k) Respects _≈_
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)

record PartialACO {ℓ₁} (X₀ : IPred Sᵢ ℓ₁) ℓ₂ : Set (a ⊔ lsuc ℓ₂ ⊔ ℓ ⊔ ℓ₁) where
  field
    B          : ℕ → IPred Sᵢ ℓ₂

    X₀≋B₀      : X₀ ≋ᵢ B 0
    
    Bᵢ-cong    : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
    F-resp-B₀  : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
    F-mono-B   : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)

    -- There exists a point k* after which the boxes only contain x*
    x*         : S
    k*         : ℕ
    B-finish   : ∀ {k} → k* ≤ k → Singletonᵢ _≈_ (B k) x*

  B-cong : ∀ {k} → (_∈ᵢ B k) Respects _≈_
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)

ACO⇒partialACO : ∀ {ℓ₃} → ACO ℓ₃ → PartialACO Uᵢ ℓ₃
ACO⇒partialACO aco = record
  { B         = B
  ; F-resp-B₀ = λ {x} x∈B₀ → λ i → B₀-universal i (F x i) 
  ; X₀≋B₀     = (λ _ → B₀-universal _ _) , λ _ → tt
  ; Bᵢ-cong   = Bᵢ-cong
  ; F-mono-B  = F-mono-B
  ; x*        = x*
  ; k*        = k*
  ; B-finish  = B-finish
  } where open ACO aco

partialACO⇒ACO : ∀ {ℓ₁ ℓ₃} {X₀ : IPred Sᵢ ℓ₁} →
                 Universalᵢ X₀ →
                 PartialACO X₀ ℓ₃ → ACO ℓ₃
partialACO⇒ACO _∈X₀ pACO = record
  { B            = B
  ; Bᵢ-cong      = Bᵢ-cong
  ; B₀-universal = λ i x → proj₁ X₀≋B₀ (x ∈X₀)
  ; F-mono-B     = F-mono-B
  ; x*           = x*
  ; k*           = k*
  ; B-finish     = B-finish
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


record PartialSynchronousConditions {p} (B : IPred Sᵢ p) o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

  field
    Bᵢ-cong           : ∀ {i} → (_∈ B i) Respects _≈ᵢ_
    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

  _≤ₛ_ : Rel S _
  x ≤ₛ y = ∀ i → x i ≤ᵢ y i

  field
    B-closed          : ∀ {x} → x ∈ᵢ B → F x ∈ᵢ B
    F-monotone        : ∀ {x y} → x ∈ᵢ B → y ∈ᵢ B → x ≤ₛ y → F x ≤ₛ F y
    F-decreasing      : ∀ {x} → x ∈ᵢ B → F x ≤ₛ x
    
    -- σ converges to a unique fixed point
    x*                : S
    x*-fixed          : F x* ≈ x*
    k*                : ℕ
    σ-convergesTo-x*  : ∀ {x} → x ∈ᵢ B → σ k* x ≈ x*
    
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

  B-cong : (_∈ᵢ B) Respects _≈_
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)





sync⇒partialSync : ∀ {ℓ₃} → SynchronousConditions ℓ₃ → PartialSynchronousConditions Uᵢ ℓ₃
sync⇒partialSync sync = record
  { Bᵢ-cong           = λ _ _ → tt
  ; _≤ᵢ_              = _≤ᵢ_
  ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder
  ; B-closed          = λ _ _ → tt
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
    B₀                : Pred Sᵢ p
    B₀-cong           : ∀ {x y} → x ∈ B₀ → x ≈ y → y ∈ B₀
    B₀-closed         : ∀ {x} → x ∈ B₀ → F x ∈ B₀
    B₀-finite         : ∃ λ xs → ∀ {x} → x ∈ B₀ → x ∈L xs

    -- ξ∈B₀              : ξ ∈ B₀

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
    ξ∈B₀            : ξ ∈ B₀
    F-strictlyDecr  : ∀ {x} → x ∈ B₀ → x ≉ ξ → F x < x
    F-monotone      : ∀ {x y} → x ∈ B₀ → y ∈ B₀ → x ≤ y → F x ≤ F y
    F-cong          : ∀ {x y} → x ≈ y → F x ≈ F y
-}
