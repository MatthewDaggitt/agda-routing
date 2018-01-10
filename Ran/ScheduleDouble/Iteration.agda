-- imports
open import Data.Nat
  using (ℕ; _<_; zero; suc; _≤_; s≤s)
open import Data.Fin
  using (Fin)
open import Schedule
  using (𝕋)
open import ScheduleDouble
  using (ScheduleDouble)
open import Computation
  using (Computation)
open import Induction.WellFounded
  using (Acc; acc)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no)
open import Data.Nat.Properties
  using (≤-reflexive)
open import Relation.Binary.PropositionalEquality
  using (_≡_) renaming (refl to ≡refl)
open import Relation.Binary
  using (Setoid)
open import Induction.Nat
  using (<-well-founded)

module ScheduleDouble.Iteration {a}{ℓ}{n : ℕ}{S : Fin n → Setoid a ℓ}(s : ScheduleDouble n)(c : Computation S) where
  open ScheduleDouble.ScheduleDouble s
  open Computation.Computation c
  open Setoid
  
  -- Asynchronous iteration
  async-iter : (t : 𝕋) → ((j : Fin n) → Carrier (S j))
             → Acc _<_ t → (i : Fin n) → Carrier (S i)
  async-iter zero x₀ _ i = x₀ i
  async-iter (suc t) x₀ (acc rs) i with i ∈? α (suc t)
  ... | yes _ = f (λ (j : Fin n) →
      async-iter (β (suc t) i j) x₀ (rs (β (suc t) i j) (s≤s (causality t i j))) j) i
  ... | no  _ = async-iter t x₀ (rs t (≤-reflexive ≡refl)) i

