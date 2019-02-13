open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product
open import Level using (_⊔_) renaming (zero to ℓ₀; suc to lsuc)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (U)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Asynchronous
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.Indexed.Homogeneous

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3-Counterexample where

---------------------------------------------------------
-- The synchronous conditions as described by U&D.

  record SynchronousConditions {a ℓ n} {𝕊 : Setoid (Fin n) a ℓ} (P : Parallelisation 𝕊) p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where

    open Parallelisation P

    field
      D₀               : Pred Sᵢ p
      D₀-cong          : ∀ {x y} → x ∈ D₀ → x ≈ y → y ∈ D₀
      D₀-closed        : ∀ {x} → x ∈ D₀ → F x ∈ D₀

      _≤ᵢ_              : Rel Sᵢ o
      ≤ᵢ-isPartialOrder : IsPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

    open IsPartialOrder ≤ᵢ-isPartialOrder public
    _≤_ = Lift Sᵢ _≤ᵢ_

    field
      F-monotone       : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≤ y → F x ≤ F y
      F-cong           : ∀ {x y} → x ≈ y → F x ≈ F y
      iter-decreasing  : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x (suc K) ≤ syncIter x K
      iter-converge    : ∀ {x} → x ∈ D₀ → ∃ λ T → ∀ t → syncIter x T ≈ syncIter x (T + t)


  ---------------------------------------------------------
  -- We now construct a counterexample that obeys the
  -- above conditions but does not converge to a unique
  -- fixed point

  -- The counterexample is two incomparable elements each
  -- of which is a fixed point for F.

  data S : Set where
    a : S
    b : S


  Sᵢ : Fin 1 → Set _
  Sᵢ i = S

  module _ where

    -- abstract

    data _≤ᵢ_ : B.Rel S ℓ₀ where
      ≤-refl : ∀ {s} → s ≤ᵢ s

    ≤ᵢ-isPartialOrder : IsPartialOrder Sᵢ _≡_ _≤ᵢ_
    ≤ᵢ-isPartialOrder = record
      { isPreorderᵢ = record
        { isEquivalenceᵢ = record
          { reflᵢ  = refl
          ; symᵢ   = sym
          ; transᵢ = trans
          } --isEquivalence
        ; reflexiveᵢ     = λ { refl → ≤-refl }
        ; transᵢ         = λ { ≤-refl ≤-refl → ≤-refl }
        }
      ; antisymᵢ         = λ { ≤-refl _ → refl }
      }

    _≤_ = Lift Sᵢ _≤ᵢ_


  𝕊 : Setoid (Fin 1) _ _
  𝕊 = record
    { Carrierᵢ       = Sᵢ
    ; _≈ᵢ_           = _≡_
    ; isEquivalenceᵢ = record
      { reflᵢ  = refl
      ; symᵢ   = sym
      ; transᵢ = trans
      }
    }


  F : Table S 1 → Table S 1
  F x = x

  F∥ : Parallelisation 𝕊
  F∥ = record { F = F }

  open Parallelisation F∥ hiding (F; Sᵢ) renaming (S to T)

  F-cong : ∀ {x y} → x ≈ y → F x ≈ F y
  F-cong x≈y = x≈y

  D₀ : Pred Sᵢ _
  D₀ {i} x = U x

  _∈D₀ : T → Set _
  x ∈D₀ = ∀ i → D₀ {i} (x i)

  D₀-cong : ∀ {x y} → x ∈D₀ → x ≈ y → y ∈D₀
  D₀-cong {_} {y} _ _ i = U-Universal (y i)

  D₀-closed : ∀ {s} → s ∈D₀ → F s ∈D₀
  D₀-closed {s} s∈D₀ i = U-Universal (s i)

  F-monotone : ∀ {x y} → x ∈D₀ → y ∈D₀ → x ≤ y → F x ≤ F y
  F-monotone _ _ x≼y i = x≼y i

  syncIter-id : ∀ x t i → x i ≡ syncIter x t i
  syncIter-id x zero    i = refl
  syncIter-id x (suc t) i = syncIter-id x t i

  iter-decreasing : ∀ {x} → x ∈D₀ → ∀ K → syncIter x (suc K) ≤ syncIter x K
  iter-decreasing _ K i = ≤-refl

  iter-converge : ∀ {x} → x ∈D₀ → ∃ λ T → ∀ t → syncIter x T ≈ syncIter x (T + t)
  iter-converge {x} _ = 0 , syncIter-id x

  syncConditions : SynchronousConditions F∥ _ _
  syncConditions = record
    { D₀                = λ {i} → D₀ {i}
    ; D₀-cong           = D₀-cong
    ; D₀-closed         = λ {s} → D₀-closed {s}
    ; _≤ᵢ_              = _≤ᵢ_
    ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder
    ; F-monotone        = F-monotone
    ; F-cong            = F-cong
    ; iter-decreasing   = iter-decreasing
    ; iter-converge     = iter-converge
    }

  -- But

  a-convergesTo-a : F (λ _ → a) ≡ (λ _ → a)
  a-convergesTo-a = refl

  b-convergesTo-b : F (λ _ → b) ≡ (λ _ → b)
  b-convergesTo-b = refl

