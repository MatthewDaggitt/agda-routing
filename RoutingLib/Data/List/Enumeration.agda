open import Data.List using (List)
import Data.List.Any.Membership as Membership
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

import RoutingLib.Data.List.Uniqueness as Uniqueness
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Table.Relation.Equality using (𝕋ₛ)

module RoutingLib.Data.List.Enumeration where

  record Finite {a ℓ} (S : Setoid a ℓ) : Set (a ⊔ ℓ) where

    open Setoid S renaming (Carrier to A)
    open Membership S using (_∈_)
    open Uniqueness S using (Unique)
    
    field
      list     : List A
      complete : ∀ (a : A) → a ∈ list
      unique   : Unique list

  postulate tabulate : ∀ {a} {A : Set a} → List A → ∀ n → List (Table A n)
  --tabulate xs = {!!}


  postulate tablesFinite : ∀ {a ℓ} {S : Setoid a ℓ} → Finite S → ∀ n → Finite (𝕋ₛ S n)
  {-
  tabulate2 {S = S} S-fin n = record
    { list     = tabulate list n
    ; complete = {!!}
    ; unique   = {!!}
    }
    where
    open Finite S-fin
  -}
