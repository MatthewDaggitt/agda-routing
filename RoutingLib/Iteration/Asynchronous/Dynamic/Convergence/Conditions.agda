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
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Metric
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid_at_)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEq
open import RoutingLib.Relation.Unary.Indexed hiding (_∉_)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
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
    B          : Epoch → Subset n → ℕ → IPred Sᵢ p
    B₀-eqᵢ     : ∀ {e p} f q {i xᵢ} → xᵢ ∈ᵤ B e p 0 i → xᵢ ∈ᵤ B f q 0 i
    Bᵢ-cong    : ∀ {e p k i} → (_∈ᵤ B e p k i) Respects _≈ᵢ_
    B-finish   : ∀ e p → ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ B e p k × (∀ {x} → x ∈ B e p k → x ≈ x*))
    B-null     : ∀ {e p k i} → i ∉ p → ⊥ i ∈ᵤ B e p k i

    -- Properties of F in relation to the boxes
    F-resp-B₀  : ∀ {e p x} → x ∈ B e p 0 → F e p x ∈ B e p 0
    F-mono-B   : ∀ {e p k x} → WellFormed p x → x ∈ B e p k → F e p x ∈ B e p (suc k)

  B₀ : IPred Sᵢ p
  B₀ = B 0 ⊤ 0
  
--------------------------------------------------------------------------------
-- Ultrametric spaces --
--------------------------------------------------------------------------------
-- Ultrametic space conditions that are also sufficient (and necessary)
-- conditions as defined by Gurney

record UltrametricConditions : Set (a ⊔ ℓ) where
  field
    dᵢ                 : Epoch → Subset n → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
    dᵢ-cong            : ∀ e p {i} → (dᵢ e p {i}) Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
    x≈y⇒dᵢ≡0           : ∀ e p {i} {x y : Sᵢ i} → x ≈ᵢ y → dᵢ e p x y ≡ 0
    dᵢ≡0⇒x≈y           : ∀ e p {i} {x y : Sᵢ i} → dᵢ e p x y ≡ 0 → x ≈ᵢ y
    dᵢ-bounded         : ∀ e p → ∃ λ dₘₐₓ → ∀ {i} x y → dᵢ e p {i} x y ≤ dₘₐₓ -- TO-DO
    element            : S

  dₛᵢ : Epoch → Subset n → ∀ {i} → Sᵢ i → Sᵢ i → ℕ
  dₛᵢ e p {i} x y = if ⌊ i ∈? p ⌋ then dᵢ e p x y else 0
  
  d : Epoch → Subset n → S → S → ℕ
  d e p x y = max 0 (λ i → dₛᵢ e p (x i) (y i))

  field
    F-strContrOnOrbits  : ∀ e p {x} → WellFormed p x → F e p x ≉[ p ] x → d e p (F e p x) (F e p (F e p x)) < d e p x (F e p x)
    F-strContrOnFP      : ∀ e p {x} → WellFormed p x → ∀ {x*} → F e p x* ≈ x* → x ≉[ p ] x* → d e p x* (F e p x) < d e p x* x
    F-inactive          : ∀ e {p} x → WellFormed p (F e p x)



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
