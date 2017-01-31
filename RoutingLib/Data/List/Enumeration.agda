open import Level using (_⊔_)
open import Data.List using (List)
open import Data.List.Any as Any using (module Membership)
open import Relation.Binary using (Setoid)

open import RoutingLib.Data.List.All.Uniqueness


module RoutingLib.Data.List.Enumeration {c} {ℓ} (S : Setoid c ℓ) where

  open Setoid S using () renaming (Carrier to A)


  record IsEnumeration (values : List A) : Set (c ⊔ ℓ) where

    open Membership S using (_∈_)

    field
      unique : Unique S values
      complete : ∀ x → x ∈ values


  record Enumeration : Set (c ⊔ ℓ) where

    field
      list : List A
      isEnumeration : IsEnumeration list

    open IsEnumeration isEnumeration public
