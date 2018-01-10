module Computation where

  -- Imports
  open import Data.Nat
    using (ℕ; zero; suc; _<_; _≤_; _+_)
  open import Data.Fin
    using (Fin) renaming (zero to fzero; suc to fsuc)
  open import Relation.Unary
    using (Pred; _∈_; _∉_; _⊆_; ｛_｝)
  open import Level
    using (_⊔_) renaming (zero to lzero; suc to lsuc)
  open import Data.Product
    using (_×_; ∃)
  open import Relation.Binary.PropositionalEquality
    using (_≢_; _≡_)
  open import Relation.Binary
    using (Setoid)
  open import Relation.Binary.Core
    using (Substitutive)
  open Setoid

  -- Computations
  record Computation {a}{ℓ}{n : ℕ}(S : Fin n → Setoid a ℓ) : Set (lsuc (a ⊔ ℓ)) where
    field
      f : ((j : Fin n) → (Carrier (S j))) → (i : Fin n) → (Carrier (S i))

  -- Asynchronously Contracting Operators (ACO)
  record ACO {a}{ℓ}{n : ℕ}{S : Fin n → Setoid a ℓ}(c : Computation S)
    : Set (lsuc (lsuc (a ⊔ ℓ))) where
    open Computation c
    field
      M          : ℕ
      D          : ℕ → ∀ i → Pred (Carrier (S i)) a
      D-monotone : ∀ K → K < M → (∀ i →
                 (∀ (dᵢ : Carrier (S i)) → dᵢ ∈ D (suc K) i → dᵢ ∈ D K i)) ×
                 (∃ λ i → ∃ λ dᵢ' → dᵢ' ∈ D K i × dᵢ' ∉ D (suc K) i)
      D-finish   : ∃ λ (ξ : (i : Fin n) → Carrier (S i)) → (∀ K i → ξ i ∈ D (M + K) i) ×
                            (∀ {x : (i : Fin n) → Carrier (S i)} K i → x i ∈ D (M + K) i →
                            (_≈_ (S i)) (x i) (ξ i))
      c-monotone : ∀ K → {x : ∀ i → Carrier (S i)} → (∀ i → x i ∈ D K i) →
                 (∀ i → f x i ∈ D (suc K) i)
      D-subst : ∀ K i x y → (_≈_ (S i)) x y → x ∈ D K i → y ∈ D K i
                 
