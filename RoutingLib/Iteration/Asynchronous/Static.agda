--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of what it means to be a static
-- asynchronous iteration as well as the definition of the state function
-- and what it means for such processes to be "correct".
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static where

open import Algebra.FunctionProperties using (Congruent₁)
open import Level using (_⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Fin.Subset using (Subset) renaming (_∉_ to _∉ₛ_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary as B using (Setoid; Rel; _Preserves_⟶_; Reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _∈_; U)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Binary.Equality as TableEquality
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FiniteSubset
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as FiniteSubsetEquality
open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_; Uᵢ; Universalᵢ)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule as Schedules
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod

------------------------------------------------------------------------
-- Parallelisable functions

record IsAsyncIterable
  {a n ℓ}
  -- Types for state of each node
  {Sᵢ : Fin n → Set a}
  -- Equality for the type of each node
  (_≈ᵢ_ : IRel Sᵢ ℓ)
  -- The set of functions indexed by epoch and participants
  (F : (∀ i → Sᵢ i) → (∀ i → Sᵢ i))
  : Set (a ⊔ ℓ) where

  -- The type of the global state of the computation
  S : Set _
  S = ∀ i → Sᵢ i

  -- Global equality
  _≈_ : Rel S ℓ
  x ≈ y = ∀ i → x i ≈ᵢ y i

  _≉_ : Rel S ℓ
  x ≉ y = ¬ (x ≈ y)

  -- Required assumptions
  field
    isDecEquivalenceᵢ : IsIndexedDecEquivalence Sᵢ _≈ᵢ_
    F-cong            : F Preserves _≈_ ⟶ _≈_

  -- Re-export various forms of equality
  ≈-iDecSetoid : IndexedDecSetoid (Fin n) a ℓ
  ≈-iDecSetoid = record { isDecEquivalenceᵢ = isDecEquivalenceᵢ }

  open IndexedDecSetoid ≈-iDecSetoid public
    using (_≟ᵢ_)
    renaming
    ( reflexiveᵢ    to ≈ᵢ-reflexive
    ; reflexive     to ≈-reflexive
    ; reflᵢ         to ≈ᵢ-refl
    ; refl          to ≈-refl
    ; symᵢ          to ≈ᵢ-sym
    ; sym           to ≈-sym
    ; transᵢ        to ≈ᵢ-trans
    ; trans         to ≈-trans
    ; isEquivalence to ≈-isEquivalence
    ; setoid        to ≈-setoid
    ; indexedSetoid to ≈ᵢ-iSetoid
    )

  _≟_ : B.Decidable _≈_
  x ≟ y = all? (λ i → x i ≟ᵢ y i)

  open FiniteSubsetEquality ≈-iDecSetoid public hiding (_≈[_]_)


record AsyncIterable a ℓ n : Set (lsuc a ⊔ lsuc ℓ) where
  field
    Sᵢ               : Fin n → Set a
    _≈ᵢ_             : IRel Sᵢ ℓ
    F                : (∀ i → Sᵢ i) → (∀ i → Sᵢ i)
    isAsyncIterable  : IsAsyncIterable _≈ᵢ_ F

  open IsAsyncIterable isAsyncIterable public

-------------------------------------------------------------------------
-- Dynamic asynchronous state function
--
-- Given an iterable and a schedule and an initial state, returns the
-- state at time t.

module _ {a ℓ n} (I∥ : AsyncIterable a ℓ n) (ψ : Schedule n) where

  open AsyncIterable I∥
  open Schedule ψ

  -- The six cases (in-order)
  -- 1. Initially: not participating
  -- 2. Initially: participating
  -- 3. Currently: not participating
  -- 4. Currently: just started participating
  -- 5. Currently: participating but inactive
  -- 6. Currently: participating and active
  asyncIter' : S → ∀ {t} → Acc _<_ t → S
  asyncIter' x₀ {zero} _ i = x₀ i
  asyncIter' x₀ {suc t} (acc rec) i with i ∈? α (suc t)
  ... | no  _ = asyncIter' x₀ (rec t ≤-refl) i
  ... | yes _ = F (λ j → asyncIter' x₀ (rec (β (suc t) i j) (s≤s (β-causality t i j))) j) i

  asyncIter : S → 𝕋 → S
  asyncIter x₀ t = asyncIter' x₀ (<-wellFounded t)


-------------------------------------------------------------------------
-- The notion of correctness for static parallelisations

module _ {a ℓ n} (I∥ : AsyncIterable a ℓ n) where

  open AsyncIterable I∥

  record Converges : Set (lsuc 0ℓ ⊔ a ⊔ ℓ) where
    field
      x*         : S
      k*         : ℕ
      x*-fixed   : F x* ≈ x*
      x*-reached : ∀ x → (ψ : Schedule n) →
                   ∀ {s e : 𝕋} → MultiPseudocycle ψ k* [ s , e ] →
                   ∀ {t} → e ≤ t →
                   asyncIter I∥ ψ x t ≈ x*

  record PartiallyConverges {p} (X₀ : IPred Sᵢ p) : Set (lsuc 0ℓ ⊔ a ⊔ ℓ ⊔ p) where
    field
      x*         : S
      k*         : ℕ
      x*-fixed   : F x* ≈ x*
      x*-reached : ∀ {x} → x ∈ᵢ X₀ →
                   (ψ : Schedule n) →
                   ∀ {s e : 𝕋} → MultiPseudocycle ψ k* [ s , e ] →
                   ∀ {t} → e ≤ t →
                   asyncIter I∥ ψ x t ≈ x*

  converges⇒partiallyConverges : Converges → PartiallyConverges Uᵢ
  converges⇒partiallyConverges conv = record
    { x*         = x*
    ; k*         = k*
    ; x*-fixed   = x*-fixed
    ; x*-reached = λ {x} _ → x*-reached x
    } where open Converges conv

  partiallyConverges⇒converges : ∀ {p} {X₀ : IPred Sᵢ p} → Universalᵢ X₀ →
                                 PartiallyConverges X₀ → Converges
  partiallyConverges⇒converges _∈X₀ partialConv = record
    { x*         = x*
    ; k*         = k*
    ; x*-fixed   = x*-fixed
    ; x*-reached = λ x → x*-reached (λ i → x i ∈X₀)
    } where open PartiallyConverges partialConv

  
  partiallyConverges⇒converges′ : PartiallyConverges Uᵢ → Converges
  partiallyConverges⇒converges′ = partiallyConverges⇒converges (λ _ → tt)
