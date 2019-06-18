open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel; Symmetric)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.List.Any using (Any)
open import Function using (_∘_)
open import Data.List using (List; []; _∷_; concat)
open import Data.List.Any.Properties using (++⁻)
open import Data.List.All using (All; []; _∷_; map)
open import Data.List.All.Properties using (¬Any⇒All¬)
open import Data.Product using (_×_; _,_; swap)
open import Data.Sum using (inj₁; inj₂)

import RoutingLib.Data.List.Membership.Setoid as Membership
open import RoutingLib.Data.List.Relation.Unary.All.Properties using (∈-All)

module RoutingLib.Data.List.Relation.Binary.Disjoint.Properties {c ℓ} (S : Setoid c ℓ) where

open Setoid S renaming (Carrier to A)
open import Data.List.Membership.Setoid S using (_∈_; _∉_)
open import Data.List.Relation.Binary.Disjoint.Setoid S

xs#[] : ∀ xs → Disjoint xs []
xs#[] _ (_ , ())
