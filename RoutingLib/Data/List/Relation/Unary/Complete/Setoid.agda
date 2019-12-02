
open import Relation.Binary

module RoutingLib.Data.List.Relation.Unary.Complete.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.List
import Data.List.Membership.Setoid as Membership
open import Level

open Setoid S renaming (Carrier to A)
open Membership S

Complete : List A → Set (a ⊔ ℓ)
Complete xs = ∀ x → x ∈ xs
