open import Algebra.FunctionProperties using (Congruent₁)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Fin.Subset using (Subset) renaming (_∉_ to _∉ₛ_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary as B using (Setoid; Rel; _Preserves_⟶_; Reflexive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construction.FiniteSubset as FiniteSubset
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construction.FiniteSubset.DecEquality as FiniteSubsetEquality
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Schedule
open import RoutingLib.Iteration.Asynchronous.Schedule.Pseudoperiod

module RoutingLib.Iteration.Asynchronous.Dynamic where

------------------------------------------------------------------------
-- Parallelisable functions

record IsAsyncIterable
  {a n ℓ} {Sᵢ : Fin n → Set a}
  (_≈ᵢ_ : IRel Sᵢ ℓ)
  (F : Epoch → Subset n → (∀ i → Sᵢ i) → (∀ i → Sᵢ i))
  (⊥ : (∀ i → Sᵢ i))
  : Set (a ⊔ ℓ) where
  
  open FiniteSubset Sᵢ _≈ᵢ_ using () renaming (_∼[_]_ to _≈[_]_) public

  S : Set _
  S = ∀ i → Sᵢ i
  
  WellFormed : Subset n → S → Set _
  WellFormed p x = ∀ {i} → i ∉ₛ p → x i ≈ᵢ ⊥ i
  
  field
    isDecEquivalenceᵢ : IsIndexedDecEquivalence Sᵢ _≈ᵢ_
    F-cong           : ∀ e p → (F e p) Preserves _≈[ p ]_ ⟶ _≈[ p ]_
    F-inactive       : ∀ e {p} x → WellFormed p (F e p x)
    
  _≈_ : Rel S ℓ
  x ≈ y = ∀ i → x i ≈ᵢ y i

  ≈-iDecSetoid : IndexedDecSetoid (Fin n) a ℓ
  ≈-iDecSetoid = record { isDecEquivalenceᵢ = isDecEquivalenceᵢ }
  
  open IndexedDecSetoid ≈-iDecSetoid public
    using (_≟ᵢ_)
    renaming
    ( reflexiveᵢ    to ≈ᵢ-reflexive
    ; reflexive    to ≈-reflexive
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


record AsyncIterable a ℓ n : Set (lsuc a ⊔ lsuc ℓ) where
  field
    Sᵢ               : Fin n → Set a
    _≈ᵢ_             : IRel Sᵢ ℓ
    ⊥                : ∀ i → Sᵢ i
    F                : Epoch → Subset n → (∀ i → Sᵢ i) → (∀ i → Sᵢ i)
    isAsyncIterable  : IsAsyncIterable _≈ᵢ_ F ⊥

  open IsAsyncIterable isAsyncIterable public

-------------------------------------------------------------------------
-- State function
--
-- Given an iterable and a schedule and an initial state, returns the
-- state at time t.

module _ {a ℓ n} (𝓘 : AsyncIterable a ℓ n) (𝓢 : Schedule n) where

  open AsyncIterable 𝓘
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
  ... | yes _ | yes _ | yes _ = F (η (suc t)) (ρ (suc t)) (λ j → asyncIter' x₀ (rec (β (suc t) i j) (s≤s (β-causality t i j))) j) i
    
  asyncIter : S → 𝕋 → S
  asyncIter x₀ t = asyncIter' x₀ (<-wellFounded t)


-------------------------------------------------------------------------
-- Safeness of parallelisations

module _ {a ℓ n} (𝓘 : AsyncIterable a ℓ n) where

  open AsyncIterable 𝓘

  record IsSafeOver {b} (X : IPred Sᵢ b) : Set (lsuc lzero ⊔ a ⊔ ℓ ⊔ b) where
    field
      m*         : Epoch → Subset n → S
      m*-reached : ∀ {x₀} → x₀ ∈ X → (𝓢 : Schedule n) → {s : 𝕋} →
                   ∃ λ k → ∀ {m e : 𝕋} → 
                   IsConvergentPeriod 𝓢 k [ s , m ] →
                   IsSubEpoch 𝓢 [ m , e ] →
                   asyncIter 𝓘 𝓢 x₀ e ≈ m* (Schedule.η 𝓢 s) (Schedule.ρ 𝓢 s)

  IsSafe : Set (lsuc lzero ⊔ a ⊔ ℓ)
  IsSafe = IsSafeOver (U Sᵢ)

-------------------------------------------------------------------------
-- Bisimilarity

module _ {a₁ a₂ ℓ₁ ℓ₂ n} (𝓘₁ : AsyncIterable a₂ ℓ₂ n) (𝓘₂ : AsyncIterable a₂ ℓ₂ n) where

  record Bisimilar : Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where

    private
      module P = AsyncIterable 𝓘₁
      module Q = AsyncIterable 𝓘₂

{-
    field
      toᵢ      : ∀ {i} → P.Sᵢ i → Q.Sᵢ i
      fromᵢ    : ∀ {i} → Q.Sᵢ i → P.Sᵢ i
      
      F-cong  : Congruent₁ Q._≈_ Q.F

      toᵢ-cong : ∀ {i} {x y : P.Sᵢ i} → x P.≈ᵢ y → toᵢ x Q.≈ᵢ toᵢ y
      toᵢ-fromᵢ : ∀ {i} (x : Q.Sᵢ i) → toᵢ (fromᵢ x) Q.≈ᵢ x
      toᵢ-F    : ∀ {i} (x : P.S) → toᵢ (P.F x i) Q.≈ᵢ Q.F (λ j → toᵢ (x j)) i
      
    to : P.S → Q.S
    to x i = toᵢ (x i)

    from : Q.S → P.S
    from x i = fromᵢ (x i)
-}
