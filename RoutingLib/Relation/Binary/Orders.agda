
open import Relation.Binary using (Rel)


module RoutingLib.Relation.Binary.Orders where

  Bottom : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
  Bottom _≤_ ⊥ = ∀ {a} → ⊥ ≤ a

  Top : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
  Top _≤_ ⊤ = ∀ {a} → a ≤ ⊤
