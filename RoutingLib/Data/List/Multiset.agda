open import Data.List using (List)
open import Data.Product using (_×_; ∃)
open import Relation.Binary using (Setoid; Rel)
open import Relation.Nullary using (¬_)

module RoutingLib.Data.List.Multiset {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  
  Multiset : Set a
  Multiset = List A

  -- Relations

  -- Membership
  
  open import RoutingLib.Data.List.Membership S using (_∈_; _∉_) public

  -- Subset

  infix 4 _⊆_ _⊈_ _⊂_ _⊄_

  _⊆_ : Rel Multiset _
  X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y

  _⊈_ : Rel Multiset _
  X ⊈ Y = ¬ (X ⊆ Y)
  
  _⊂_ : Rel Multiset _
  X ⊂ Y = X ⊆ Y × ∃ λ y → y ∈ Y × y ∉ X

  _⊄_ : Rel Multiset _
  X ⊄ Y = ¬ (X ⊂ Y)


  -- Equality
