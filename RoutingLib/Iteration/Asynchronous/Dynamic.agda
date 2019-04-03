--------------------------------------------------------------------------------
-- Dynamic asynchronous iterations
--
-- This module contains the definition of what it means to be a dynamic
-- asynchronous iteration as well as the definition of the state function
-- and what it means for such processes to be "correct".
--------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Dynamic where

open import Level using (_⊔_) renaming (suc to lsuc)
open import Level.Literals using (#_)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Fin.Subset using (Subset) renaming (_∉_ to _∉ₛ_)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Relation.Binary as B using (Setoid; Rel; _Preserves_⟶_; Reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Universal; Pred; _∈_; U)
open import Relation.Unary.Properties using (U-Universal)

import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset
  as FiniteSubset
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality
  as FiniteSubsetEquality
open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_; Uᵢ; Universalᵢ)
open import RoutingLib.Relation.Unary.Indexed.Properties using (Uᵢ-universal)

open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule as Schedules
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod

--------------------------------------------------------------------------------
-- Publicly re-export the notions of epochs and times so that they may
-- be imported from directly from this module.

open Schedules public using (Epoch; 𝕋)

--------------------------------------------------------------------------------
-- The definition of what it means for a function F to be able to be
-- iterated in an asynchronous environment.

record IsAsyncIterable
  {a n ℓ}
  -- The type of data in each node
  {Sᵢ : Fin n → Set a}
  -- The definition of equality for each node's type of data
  (_≈ᵢ_ : IRel Sᵢ ℓ)
  -- The set of functions indexed by epoch and participants
  (F : Epoch → Subset n → (∀ i → Sᵢ i) → (∀ i → Sᵢ i))
  -- The special state representing non-participation
  (⊥ : (∀ i → Sᵢ i))
  : Set (a ⊔ ℓ) where

  open FiniteSubset Sᵢ _≈ᵢ_ using () renaming (_∼[_]_ to _≈[_]_) public

  -- The type of the global state of the computation
  S : Set _
  S = ∀ i → Sᵢ i

  -- The definition of equality over global states
  _≈_ : Rel S ℓ
  x ≈ y = ∀ i → x i ≈ᵢ y i

  _≉_ : Rel S ℓ
  x ≉ y = ¬ (x ≈ y)

  -- Required assumptions
  field
    isDecEquivalenceᵢ : IsIndexedDecEquivalence Sᵢ _≈ᵢ_
    F-cong            : ∀ e p → (F e p) Preserves _≈_ ⟶ _≈[ p ]_

  -- The notion of a state being in agreement with a set of participants
  Accordant : Subset n → S → Set _
  Accordant p x = ∀ {i} → i ∉ₛ p → x i ≈ᵢ ⊥ i

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
    ; indexedSetoid to ≈ᵢ-setoidᵢ
    )

  _≟_ : B.Decidable _≈_
  x ≟ y = all? (λ i → x i ≟ᵢ y i)

  open FiniteSubsetEquality ≈-iDecSetoid public hiding (_≈[_]_)

-- A package that contains all the required components of an
-- async iterable
record AsyncIterable a ℓ n : Set (lsuc (a ⊔ ℓ)) where
  field
    Sᵢ               : Fin n → Set a
    _≈ᵢ_             : IRel Sᵢ ℓ
    ⊥                : ∀ i → Sᵢ i
    F                : Epoch → Subset n → (∀ i → Sᵢ i) → (∀ i → Sᵢ i)
    isAsyncIterable  : IsAsyncIterable _≈ᵢ_ F ⊥

  open IsAsyncIterable isAsyncIterable public

--------------------------------------------------------------------------------
-- State function
--------------------------------------------------------------------------------
-- Given an iterable and a schedule and an initial state, returns the
-- state at time t.

module _ {a ℓ n} (I : AsyncIterable a ℓ n) (𝓢 : Schedule n) where
  open AsyncIterable I
  open Schedule 𝓢

  -- The six cases (in-order)
  -- 1. Initially: not participating
  -- 2. Initially: participating
  -- 3. Currently: not participating
  -- 4. Currently: just started participating
  -- 5. Currently: participating but inactive
  -- 6. Currently: participating and active
  asyncIter' : S → ∀ {t} → Acc _<_ t → S
  asyncIter' x₀ {zero} _ i with i ∈? ρ 0
  ... | no  _ = ⊥  i
  ... | yes _ = x₀ i
  asyncIter' x₀ {suc t} (acc rec) i with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no _  | _     | _     = ⊥  i
  ... | yes _ | no  _ | _     = x₀ i
  ... | yes _ | yes _ | no  _ = asyncIter' x₀ (rec t ≤-refl) i
  ... | yes _ | yes _ | yes _ = F (η (suc t)) (ρ (suc t))
    (λ j → asyncIter' x₀ (rec (β (suc t) i j) (s≤s (β-causality t i j))) j) i

  asyncIter : S → 𝕋 → S
  asyncIter x₀ t = asyncIter' x₀ (<-wellFounded t)

--------------------------------------------------------------------------------
-- Convergent
--------------------------------------------------------------------------------
-- The notion of what it means for a dynamic asynchronous iteration to be
-- "correct".

module _ {a ℓ n} (I : AsyncIterable a ℓ n) where

  open AsyncIterable I
  open Schedule

  -- The definition below says that the iteration will always converge to
  -- a fixed point after a sufficiently long period of stability. Note
  -- that the definition does *not* guarantee that such a period of
  -- stability will ever occur. Hence why the property is named
  -- "Convergent" as opposed to "Converges".
  record Convergent : Set (# 1 ⊔ a ⊔ ℓ) where
    field
      -- The fixed point reached for each epoch and set of participants
      x*         : Epoch → Subset n → S
      -- The number of pseudo-cycles required to reach said fixed point
      k*         : Epoch → Subset n → ℕ
      -- The fixed points are truly fixed points
      x*-fixed   : ∀ e p → F e p (x* e p) ≈ x* e p
      -- For every schedule S , starting point x₀ and point in time tₛ,
      -- then if the schedule is k*-pseudoperiodic between t₁ and t₂
      -- then for every time t₃ after t₂ that is within the same epoch
      -- the iteration will be at the fixed point x*.
      x*-reached : ∀ (x₀ : S) (S : Schedule n) →
                   ∀ {tₛ tₘ : 𝕋} →
                   MultiPseudocycle S (k* (η S tₛ) (ρ S tₛ)) [ tₛ , tₘ ] →
                   ∀ {tₑ : 𝕋} → SubEpoch S [ tₘ , tₑ ] →
                   asyncIter I S x₀ tₑ ≈ x* (η S tₛ) (ρ S tₛ)

  -- This is a specialised definition that only guarantees the iteration
  -- is convergent when the initial state is in the set X₀ and the set of
  -- participants is always in the set Q.
  record PartiallyConvergent {ℓ₁ ℓ₂} (X₀ : IPred Sᵢ ℓ₁) (Q : Pred (Subset n) ℓ₂)
                             : Set (# 1 ⊔ a ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      x*         : Epoch → ∀ {p} → p ∈ Q → S
      k*         : Epoch → ∀ {p} → p ∈ Q → ℕ
      x*-fixed   : ∀ e {p} (p∈Q : p ∈ Q) → F e p (x* e p∈Q) ≈ x* e p∈Q
      x*-reached : ∀ {x₀} → x₀ ∈ᵢ X₀ →
                   ∀ {S : Schedule n} (ρ∈Q : S satisfies Q) →
                   ∀ {tₛ tₘ : 𝕋} →
                   MultiPseudocycle S (k* (η S tₛ) (ρ∈Q tₛ)) [ tₛ , tₘ ] →
                   ∀ {tₑ} → SubEpoch S [ tₘ , tₑ ] →
                   asyncIter I S x₀ tₑ ≈ x* (η S tₛ) (ρ∈Q tₛ)

-- The relationship between convergent and partially convergent

module _ {a ℓ n} {I : AsyncIterable a ℓ n} where

  open AsyncIterable I

  convergent⇒partiallyConvergent : Convergent I → PartiallyConvergent I Uᵢ U
  convergent⇒partiallyConvergent convergent = record
    { x*         = λ e {p} _ → x* e p
    ; k*         = λ e {p} _ → k* e p
    ; x*-fixed   = λ e {p} _ → x*-fixed e p
    ; x*-reached = λ {x₀} _ {S} _ → x*-reached x₀ S
    } where open Convergent convergent

  partiallyConvergent⇒convergent : ∀ {ℓ₁} {X₀ : IPred Sᵢ ℓ₁} → Universalᵢ X₀ →
                                   ∀ {ℓ₂} {Q : Pred (Subset n) ℓ₂} → Universal Q →
                                   PartiallyConvergent I X₀ Q → Convergent I
  partiallyConvergent⇒convergent (_∈X₀) (_∈Q) pConvergent = record
    { x*         = λ e p → x* e (p ∈Q)
    ; k*         = λ e p → k* e (p ∈Q)
    ; x*-fixed   = λ e p → x*-fixed e (p ∈Q)
    ; x*-reached = λ x₀ S → x*-reached (λ i → _ ∈X₀) (λ t → _ ∈Q)
    } where open PartiallyConvergent pConvergent

  partiallyConvergent⇒convergent′ : PartiallyConvergent I Uᵢ U → Convergent I
  partiallyConvergent⇒convergent′ = partiallyConvergent⇒convergent
    (Uᵢ-universal Sᵢ) U-Universal

--------------------------------------------------------------------------------
-- Simulation
--------------------------------------------------------------------------------
-- The notion of one asynchronous iteration simulating another. The behaviour
-- of one can therefore be reasoned about by looking at the behaviour of the
-- other.

module _ {a₁ a₂ ℓ₁ ℓ₂ n}
         (I∥ : AsyncIterable a₁ ℓ₁ n)
         (J∥ : AsyncIterable a₂ ℓ₂ n)
         where

  private
    module P = AsyncIterable I∥
    module Q = AsyncIterable J∥

  record Simulates : Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      toᵢ       : ∀ {i} → P.Sᵢ i → Q.Sᵢ i
      fromᵢ     : ∀ {i} → Q.Sᵢ i → P.Sᵢ i

      toᵢ-⊥     : ∀ {i} → toᵢ (P.⊥ i) Q.≈ᵢ Q.⊥ i
      toᵢ-cong  : ∀ {i} {x y : P.Sᵢ i} → x P.≈ᵢ y → toᵢ x Q.≈ᵢ toᵢ y
      toᵢ-fromᵢ : ∀ {i} (x : Q.Sᵢ i) → toᵢ (fromᵢ x) Q.≈ᵢ x
      toᵢ-F     : ∀ {i e p} x → toᵢ (P.F e p x i) Q.≈ᵢ Q.F e p (toᵢ ∘ x) i

    to : P.S → Q.S
    to x i = toᵢ (x i)

    from : Q.S → P.S
    from x i = fromᵢ (x i)

    to-cong : ∀ {x y : P.S} → x P.≈ y → to x Q.≈ to y
    to-cong x≈y i = toᵢ-cong (x≈y i)

    to-F : ∀ {e p} (x : P.S) → to (P.F e p x) Q.≈ Q.F e p (to x)
    to-F x i = toᵢ-F x
