open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∉_; ⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Maybe using (Eq; nothing)
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties using (+-comm; ≤⇒≤″)
open import Data.Product using (∃; ∃₂; _×_)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (if_then_else_)
import Data.List.Membership.Setoid as Membership
open import Function using (id)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary as B using (DecSetoid; _Respects_; Total; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.Indexed.Homogeneous using (Decidable; IsIndexedDecEquivalence; IndexedDecSetoid)
open import Relation.Unary using (_∈_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Metric
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid_at_)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEq
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static
open import RoutingLib.Iteration.Asynchronous.Static.Schedule
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod

module RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions
  {a ℓ n} (𝓘 : AsyncIterable a ℓ n) where

open AsyncIterable 𝓘

--------------------------------------------------------------------------------
-- Asynchronously contracting operator --
--------------------------------------------------------------------------------
-- Sufficient (and necessary conditions) for convergence
-- as inspired by Üresin and Dubois

record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
  field
    -- Boxes
    B          : ℕ → IPred Sᵢ p
    Bᵢ-cong    : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
    B-finish   : ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≈ x*))

    -- F
    F-resp-B₀  : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
    F-mono-B   : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)

  B-cong : ∀ {k} → (_∈ᵢ B k) Respects _≈_
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)

--------------------------------------------------------------------------------
-- Ultrametric spaces --
--------------------------------------------------------------------------------
-- Ultrametic space conditions that are also sufficient (and necessary)
-- conditions as defined by Gurney

record UltrametricConditions : Set (a ⊔ ℓ) where
  field
    dᵢ                 : ∀ {i} → Sᵢ i → Sᵢ i → ℕ
    dᵢ-cong            : ∀ {i} → (dᵢ {i}) Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
    x≈y⇒dᵢ≡0           : ∀ {i} {x y : Sᵢ i} → x ≈ᵢ y → dᵢ x y ≡ 0
    dᵢ≡0⇒x≈y           : ∀ {i} {x y : Sᵢ i} → dᵢ x y ≡ 0 → x ≈ᵢ y
    dᵢ-bounded         : ∃ λ dₘₐₓ → ∀ {i} x y → dᵢ {i} x y ≤ dₘₐₓ -- TO-DO
    element            : S

  d : S → S → ℕ
  d x y = max 0 (λ i → dᵢ (x i) (y i))

  field
    F-strContrOnOrbits  : ∀ {x} → F x ≉ x → d (F x) (F (F x)) < d x (F x)
    F-strContrOnFP      : ∀ {x x*} → F x* ≈ x* → x ≉ x* → d x* (F x) < d x* x



{-
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
