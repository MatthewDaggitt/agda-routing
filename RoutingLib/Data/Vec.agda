open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec
open import Data.List using (List; []; _∷_) renaming (map to mapₗ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable)

module RoutingLib.Data.Vec where

  _∉_ : ∀ {a n} {A : Set a} → A → Vec A n → Set a
  v ∉ xs = ¬ (v ∈ xs)
