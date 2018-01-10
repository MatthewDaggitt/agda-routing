open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

module RoutingLib.Data.GTable where

  GTable : ∀ {a} (n : ℕ) (A : Fin n → Set a) → Set a
  GTable n A = ∀ i → A i


open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; _<_; _≤_; _+_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃)
open import Relation.Binary using (DecSetoid; Setoid; Rel; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)

open import RoutingLib.Asynchronous.Schedule using (Schedule)
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.GTable using (GTable)
import RoutingLib.Data.Table.Relation.Equality as TableEquality

module RoutingLib.Asynchronous where

  open Schedule

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed and carried out on n separate processors 
  record Parallelisation {a ℓ n} (S : Table (Setoid a ℓ) n) : Set (lsuc a) where

    M : GTable ? ?
    M i = Setoid.Carrier (S i)
    
    --open TableEquality S renaming (_≈ₜ_ to _≈ₘ_; _≉ₜ_ to _≉ₘ_) public
    
    field
      -- The update functions: "σ X i" is the result of processor i activating on state X 
      σ      : ((j : Fin n) → (Setoid.Carrier (S j))) → (i : Fin n) → (Setoid.Carrier (S i))
      --σ-cong : σ Preserves _≈ₘ_ ⟶ _≈ₘ_
