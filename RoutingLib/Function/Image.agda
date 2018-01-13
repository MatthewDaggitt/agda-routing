open import Data.List using (List)
import Data.List.Any.Membership as Membership
open import Data.Product using (∃)
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open Setoid using (Carrier)

module RoutingLib.Function.Image where

  
  record FiniteImage {a b ℓ} {A : Set a} (S : Setoid b ℓ) (f : A → Carrier S) : Set (a ⊔ b ⊔ ℓ) where
    open Setoid S using (_≈_)
    open Membership S using (_∈_)
    
    field
      image    : List (Carrier S)
      complete : ∀ a → f a ∈ image
      sound    : ∀ {b} → b ∈ image → ∃ λ a → f a ≈ b
