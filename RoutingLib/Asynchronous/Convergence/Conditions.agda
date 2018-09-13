open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Maybe using (nothing)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties using (+-comm; ≤⇒≤″)
open import Data.Product using (∃; ∃₂; _×_)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
import Data.List.Membership.Setoid as Membership
open import Relation.Binary using (Total; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Binary.NonStrictToStrict as NonStrictToStrict

open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Metric using (IsUltrametric)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule

module RoutingLib.Asynchronous.Convergence.Conditions
  {a ℓ n} (𝓟 : Parallelisation a ℓ n)
  where

open Parallelisation 𝓟

--------------------------------------------------------------------------------
-- Asynchronously contracting operator --
--------------------------------------------------------------------------------
-- Sufficient (and necessary conditions) for convergence
-- as defined by Üresin and Dubois
record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
  field
    D             : Epoch → ℕ → IPred Sᵐᵢ p
    Dₑ-decreasing : ∀ e K → D e (suc K) ⊆[ Sᵐᵢ ] D e K
    D-finish      : ∀ e → ∃₂ λ T ξ → ∀ K → IsSingleton _≈_ (D e (T + K)) ξ
    F-monotonic   : ∀ {e t K} → t ∈ D e K → F e t ∈ D e (suc K)

    -- New axioms
    D₀-increasing : ∀ e → D e 0 ⊆[ Sᵐᵢ ] D (suc e) 0
    D₀-null       : ∀ e {i} → D e 0 {i} nothing

  Dₑ₀⊆Dₖ₊ₑ₀ : ∀ e k → D e 0 ⊆[ Sᵐᵢ ] D (k + e) 0
  Dₑ₀⊆Dₖ₊ₑ₀ e zero    x∈Dₑ i = x∈Dₑ i
  Dₑ₀⊆Dₖ₊ₑ₀ e (suc k) x∈Dₑ i = D₀-increasing (k + e) (Dₑ₀⊆Dₖ₊ₑ₀ e k x∈Dₑ) i

  Dₑ₀⊆Dₑ₊ₖ₀ : ∀ e k → D e 0 ⊆[ Sᵐᵢ ] D (e + k) 0
  Dₑ₀⊆Dₑ₊ₖ₀ e k rewrite +-comm e k = Dₑ₀⊆Dₖ₊ₑ₀ e k

  Dₑ₀-mono : ∀ {e f} → e ≤ f → D e 0 ⊆[ Sᵐᵢ ] D f 0
  Dₑ₀-mono {e} e≤f with ≤⇒≤″ e≤f
  ... | less-than-or-equal refl = Dₑ₀⊆Dₑ₊ₖ₀ e _
{-
--------------------------------------------------------------------------------
-- Ultrametric spaces --
--------------------------------------------------------------------------------
-- Ultrametic space conditions that are also sufficient (and necessary)
-- conditions as defined by Gurney

open import RoutingLib.Function.Metric setoid
  using (Bounded; _StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

record UltrametricConditions : Set (a ⊔ ℓ) where
  field
    dᵢ                 : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

  d : S → S → ℕ
  d x y = max 0 (λ i → dᵢ (x i) (y i))

  field
    dᵢ-isUltrametric    : ∀ {i} → IsUltrametric (Setoid 𝕊 at  i) dᵢ
    F-strContrOnOrbits  : F StrContrOnOrbitsOver d
    F-strContrOnFP      : F StrContrOnFixedPointOver d
    d-bounded           : Bounded d

    element             : S
    _≟ᵢ_                : Decidable Sᵢ _≈ᵢ_
    F-cong              : F Preserves _≈_ ⟶ _≈_


---------------------------------
-- Other sufficient conditions --
---------------------------------
-- Sufficient but not necessary conditions by Üresin and Dubois

record SynchronousConditions p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

  field
    D₀               : Pred Sᵢ p
    D₀-cong          : ∀ {x y} → x ∈ D₀ → x ≈ y → y ∈ D₀
    D₀-closed        : ∀ {x} → x ∈ D₀ → F x ∈ D₀

    _≤ᵢ_              : IRel Sᵢ o
    ≤ᵢ-isPartialOrder : IsIndexedPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

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

  field
    F-monotone       : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≤ y → F x ≤ F y
    F-cong           : ∀ {x y} → x ≈ y → F x ≈ F y
    iter-decreasing  : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x (suc K) ≤ syncIter x K

    ξ                : S
    ξ-fixed          : F ξ ≈ ξ
    iter-converge    : ∀ {x} → x ∈ D₀ → ∃ λ T → syncIter x T ≈ ξ






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
