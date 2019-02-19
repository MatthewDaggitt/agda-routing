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
-- Asynchronously metricly contracting operator (AMCO)
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

record SynchronousConditions p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

  field
    B                 : IPred Sᵢ p
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

    -- B is non-empty
    xₚ                 : S
    xₚ∈B               : xₚ ∈ᵢ B
    
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
