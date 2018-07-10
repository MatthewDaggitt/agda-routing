open import Data.List using (List; []; _∷_)
open import Data.List.Any using (any)
open import Relation.Binary using (DecSetoid; Decidable)
open import Relation.Nullary using (yes; no)

module RoutingLib.Data.List.Membership.DecSetoid {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS public renaming (Carrier to A)
  open import Data.List.Membership.DecSetoid DS using (_∈?_)

  deduplicate : List A → List A
  deduplicate []       = []
  deduplicate (x ∷ xs) with x ∈? xs
  ... | yes _ = deduplicate xs
  ... | no  _ = x ∷ deduplicate xs
