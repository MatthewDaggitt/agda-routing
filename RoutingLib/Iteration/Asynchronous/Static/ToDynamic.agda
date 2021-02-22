------------------------------------------------------------------------
-- Agda routing library
--
-- This module shows that a static asynchronous iteration is merely a
-- special type of a dynamic asynchronous iteration, and therefore
-- convergence (and the associated pre-conditions) can be converted to
-- dynamic iterations and then back again.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; _∉_) renaming (⊤ to ⊤ₛ; _∈_ to _∈ₛ_)
open import Data.Fin.Subset.Properties using (_∈?_; ∈⊤)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Maybe using (Maybe; just; nothing; to-witness; Is-just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Level using (0ℓ; lift; _⊔_)
open import Relation.Binary using (Rel; _Respects_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel; Lift)
open import Relation.Nullary using (Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; U; _∈_)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Data.Fin.Subset using (Full)
open import RoutingLib.Data.Fin.Subset.Properties using (⊤-full)
open import RoutingLib.Data.Maybe.Properties
open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_; _⊆ᵢ_; _≋ᵢ_; Uᵢ)
open import RoutingLib.Relation.Unary.Indexed.Construct.Add.Point.Exclude
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FiniteSubset
open import RoutingLib.Relation.Nullary.Indexed.Construct.Add.Point
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.Add.Point.Equality.DecSetoid
  as LiftedEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.At using (_atₛ_)

import RoutingLib.Iteration.Asynchronous.Dynamic as Dynamic
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions as Dynamic
import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule as Dynamic
import RoutingLib.Iteration.Asynchronous.Static.Schedule as Static
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudocycle as Static
import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions as Static
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
  using (Epoch; 𝕋) renaming ([_,_] to [_,_]ₜ)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.FromStatic
import RoutingLib.Iteration.Asynchronous.Static as Static

module RoutingLib.Iteration.Asynchronous.Static.ToDynamic
  {a ℓ n} (I∥ : Static.AsyncIterable a ℓ n)
  (open Static.AsyncIterable I∥)
  (⊥ : S)
  where

open Dynamic.AsyncIterable using (Accordant)
  
------------------------------------------------------------------------
-- Formulating the dynamic iteration
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The iteration can then be lifted as well

open FiniteSubset Sᵢ _≈ᵢ_ using () renaming (_∼[_]_ to _≈[_]_)
  
F∙-cong : ∀ (p : Subset n) → F Preserves _≈_ ⟶ _≈[ p ]_
F∙-cong = {!!}

F∙-isAsyncIterable : Dynamic.IsAsyncIterable _≈ᵢ_ (λ _ _ → F) ⊥
F∙-isAsyncIterable = record
  { isDecEquivalenceᵢ = isDecEquivalenceᵢ
  ; F-cong            = λ _ → F∙-cong
  }

I∙∥ : Dynamic.AsyncIterable a ℓ n
I∙∥ = record
  { isAsyncIterable = F∙-isAsyncIterable
  }

------------------------------------------------------------------------
-- The dynamic iteration mirrors the static iteration

module _ (ψ : Static.Schedule n) where

  open Static.Schedule ψ
  
  asyncIter-sim : ∀ x₀ {t} (accₜ : Acc _<_ t) →
                  Static.asyncIter' I∥ ψ x₀ accₜ ≈
                  Dynamic.asyncIter' I∙∥ (convert ψ) x₀ accₜ
  asyncIter-sim x₀ {zero} rec i with i ∈? ⊤ₛ
  ... | yes _   = ≈ᵢ-refl
  ... | no  i∉⊤ = contradiction ∈⊤ i∉⊤
  asyncIter-sim x₀ {suc t} (acc rec) i with i ∈? ⊤ₛ | i ∈? α (suc t)
  ... | no  i∉⊤ | _     = contradiction ∈⊤ i∉⊤
  ... | yes _   | no  _ = asyncIter-sim x₀ (rec t _) i
  ... | yes _   | yes _ = F-cong (λ j → asyncIter-sim x₀ (rec (β (suc t) i j) _) j) i

------------------------------------------------------------------------
-- If the dynamic iteration converges then the static iteration
-- converges

module DynamicToStaticConvergence
  (C : Dynamic.PartiallyConvergent I∙∥ Uᵢ U)
  (x : S)
  where

  open Dynamic.PartiallyConvergent C
  open Dynamic.LocalFixedPoint (localFP {0} {⊤ₛ} _)

  x*-reached : ∀ (x₀ : S) →
                ∀ (ψ : Static.Schedule n) →
                ∀ {s m : 𝕋} →
                Static.MultiPseudocycle ψ k* [ s , m ]ₜ →
                ∀ {e} → m ≤ e →
                Static.asyncIter I∥ ψ x₀ e ≈ x*
  x*-reached x₀ ψ mpp {e} m≤e = begin
    Static.asyncIter  I∥  ψ  x₀ e  ≈⟨ asyncIter-sim ψ x₀ (<-wellFounded e) ⟩
    Dynamic.asyncIter I∙∥ ψᵈ x₀ e  ≈⟨ reachesFP _ _ _ ψᵈ-mpp ψᵈ-η[m,e] ⟩
    x*                             ∎
    where
    open EqReasoning ≈-setoid
    ψᵈ        = convert ψ
    ψᵈ-full   = convert∈Full ψ
    ψᵈ-mpp    = convert-multiPseudocycle ψ mpp
    ψᵈ-η[m,e] = convert-subEpoch ψ m≤e

  dynamicToStaticConvergence : Static.Converges I∥
  dynamicToStaticConvergence = record
    { x*         = x*
    ; k*         = k*
    ; x*-fixed   = x*-fixed
    ; x*-reached = x*-reached
    }

open DynamicToStaticConvergence public using (dynamicToStaticConvergence)

------------------------------------------------------------------------
-- Translation from static ACO to a dynamic ACO

module StaticToDynamicACO
  {ℓ₁} (X₀ : IPred Sᵢ ℓ₁)
  {ℓ₂} (aco : Static.PartialACO I∥ X₀ ℓ₂) (open Static.PartialACO aco)
  (⊥∈X₀ : ⊥ ∈ᵢ X₀)
  where

  open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Properties.ACO I∥ aco
  
  -- Main boxes
  module _ {e : Epoch} {p : Subset n} .(p∈Full : p ∈ Full) where

    B-null : ∀ {k i} → i ∉ p → ⊥ i ∈ B k i
    B-null {i = i} i∉p = contradiction (recompute (i ∈? p) (p∈Full i)) i∉p
   
    B∙-finish : ∃₂ λ k*₁ x*₁ → (x*₁ ∈ᵢ X₀) × (∀ {k : ℕ} → k*₁ ≤ k →
                      (x*₁ ∈ᵢ B k) ×
                      (∀ {x} →
                       x ∈ᵢ B k → x ≈ x*₁))
    B∙-finish = k* , x* , x*∈X₀ ⊥∈X₀ , B-finish

    localACO : Dynamic.LocalACO I∙∥ X₀ e p ℓ₂
    localACO = record
      { B            = B
      ; Bᵢ-cong      = Bᵢ-cong
      ; B-finish     = B∙-finish
      ; B-null       = B-null
      ; F-mono-B     = λ _ _ → F-mono-B
      ; X₀⊆B₀        = proj₁ X₀≋B₀
      }

  F-pres-X₀ : ∀ {x} → x ∈ᵢ X₀ → F x ∈ᵢ X₀
  F-pres-X₀ = {!F!}
  
  dynamicACO : Dynamic.PartialACO I∙∥ {ℓ₁} X₀ {0ℓ} (λ {(e , p) → Full p}) ℓ₂
  dynamicACO = record
    { localACO  = λ {e} {p} ep∈v → {!localACO  {e} {p} ?!}
    ; F-pres-X₀ = {!F-pres-B!}
    ; ⊥∈X₀      = ⊥∈X₀
    }

open StaticToDynamicACO public
  using () renaming (dynamicACO to staticToDynamicACO)
