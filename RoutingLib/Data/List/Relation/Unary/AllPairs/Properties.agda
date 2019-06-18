open import Data.List hiding (any)
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.AllPairs.Properties
import Data.List.All.Properties as All
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Total; Symmetric; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Function
open import RoutingLib.Data.List using (insert)
import RoutingLib.Data.List.Relation.Unary.All.Properties as All
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.List.Relation.Unary.AllPairs.Properties where

------------------------------------------------------------------------
-- deduplicate

module _ {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS renaming (Carrier to A)
  open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
  open import Data.List.Membership.DecSetoid DS using (_∈?_)

  deduplicate⁺ : ∀ {ℓ} {_~_ : Rel A ℓ} {xs} → AllPairs _~_ xs →
                 AllPairs _~_ (deduplicate xs)
  deduplicate⁺ {xs = _}      [] = []
  deduplicate⁺ {xs = x ∷ xs} (px ∷ pxs) with x ∈? xs
  ... | yes _ = deduplicate⁺ pxs
  ... | no  _ = All.deduplicate⁺ DS px ∷ deduplicate⁺ pxs
