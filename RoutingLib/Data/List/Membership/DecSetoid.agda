open import Data.List using (List; []; _∷_)
open import Data.List.Any using (any)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (yes; no)

import RoutingLib.Data.List.Membership.Setoid as SetoidMembership

module RoutingLib.Data.List.Membership.DecSetoid {a ℓ} (DS : DecSetoid a ℓ) where

  open DecSetoid DS public renaming (Carrier to A; setoid to S)
  
  open SetoidMembership S public
  
  deduplicate : List A → List A
  deduplicate []       = []
  deduplicate (x ∷ xs) with any (x ≟_) xs
  ... | yes _ = deduplicate xs
  ... | no  _ = x ∷ deduplicate xs
