open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
--open import Relation.Binary.Indexed using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous -- as IndexedTypes
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule

module RoutingLib.Asynchronous.Properties where

module _ {a ℓ n} {𝕊 : Setoid (Fin n) a ℓ} where

  open Setoid 𝕊 using (_≈_) renaming (Carrierᵢ to Sᵢ; Carrier to S)
  
  shrinkSafety : ∀ {P : Parallelisation 𝕊} {v} {V : Pred Sᵢ v} {W : Pred Sᵢ v} →
                 _⊆_ {A = Sᵢ} W V →
                 IsPartiallyAsynchronouslySafe P V →
                 IsPartiallyAsynchronouslySafe P W
  shrinkSafety W⊆V V-safe = record
    { m*         = m*
    ; m*-reached = λ X∈W → m*-reached (W⊆V X∈W)
    }
    where open IsPartiallyAsynchronouslySafe V-safe

  partialToTotalSafety : ∀ {P : Parallelisation 𝕊} {v} {V : Pred Sᵢ v}  →
                         (∀ x → x ∈ V) →
                         IsPartiallyAsynchronouslySafe P V →
                         IsAsynchronouslySafe P
  partialToTotalSafety total partiallySafe = record
    { m*         = m*
    ; m*-reached = λ X → m*-reached (total X)
    }
    where open IsPartiallyAsynchronouslySafe partiallySafe

  -- The empty computation is safe (phew!)
  0-IsSafe : ∀ {a ℓ} {T : Setoid (Fin 0) a ℓ} (P : Parallelisation T) →
             IsAsynchronouslySafe P
  0-IsSafe p = record { m* = λ() ; m*-reached = λ _ _ → 0 , λ _ () }





module _ {a₁ a₂ ℓ₁ ℓ₂ n} {𝕊₁ : Setoid (Fin n) a₁ ℓ₁} {𝕊₂ : Setoid (Fin n) a₂ ℓ₂}
         {P₁ : Parallelisation 𝕊₁} {P₂ : Parallelisation 𝕊₂}
         (P₁↭P₂ : Bisimilar P₁ P₂) (P₁-isSafe : IsAsynchronouslySafe P₁) where


  module P = Parallelisation P₁
  module Q = Parallelisation P₂
  
  open Bisimilar P₁↭P₂
  open IsAsynchronouslySafe P₁-isSafe
    renaming (m* to m*₁; m*-reached to m*₁-reached)

  open Schedule


  asyncIter-eq : ∀ s X → ∀ {t} (tAcc : Acc _<_ t) →
                 to (P.asyncIter' s (from X) tAcc) Q.≈ Q.asyncIter' s X tAcc
  asyncIter-eq s X {zero}  _          i = toᵢ-fromᵢ (X i)
  asyncIter-eq s X {suc t} (acc tAcc) i with i ∈? α s (suc t)
  ... | yes _ = Q.≈ᵢ-trans (toᵢ-F _) (Q.F-cong (λ j → asyncIter-eq s X (tAcc (β s (suc t) i j) _) j) i)
  ... | no  _ = asyncIter-eq s X (tAcc _ ≤-refl) i


  m*₂ : Q.S
  m*₂ = to m*₁

  m*₂-reached : ∀ X s → ∃ λ tᶜ → ∀ t → Q.asyncIter s X (tᶜ + t) Q.≈ m*₂
  m*₂-reached X s with m*₁-reached (from X) s
  ... | (tᶜ , converged) = tᶜ , (λ t i → Q.≈ᵢ-trans
    (Q.≈-sym (asyncIter-eq s X (<-wellFounded (tᶜ + t))) i)
    (toᵢ-cong (converged t i)))
  

  bisimulation : IsAsynchronouslySafe P₂
  bisimulation = record
    { m*         = m*₂
    ; m*-reached = m*₂-reached
    }
