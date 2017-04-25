open import Data.Nat using (zero; suc)
open import Data.List
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary using (Rel)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Function using (_∘_)

open import RoutingLib.Data.List

module RoutingLib.Data.List.Properties where

  tabulate-cong : ∀ {n a ℓ} {A : Set a} {_≈_ : Rel A ℓ} (f g : Fin n → A) → (∀ i → f i ≈ g i) → ListRel _≈_ (tabulate f) (tabulate g)
  tabulate-cong {zero}  f g f≈g = []
  tabulate-cong {suc n} f g f≈g = f≈g fzero ∷ tabulate-cong (f ∘ fsuc) (g ∘ fsuc) (f≈g ∘ fsuc)
