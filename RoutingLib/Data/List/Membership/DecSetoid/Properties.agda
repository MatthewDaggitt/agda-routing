open import Relation.Binary using (DecSetoid; Setoid)
open import Relation.Nullary using (yes; no)
open import Data.List hiding (any)
open import Data.List.Any using (here; there; any)
import Data.List.Any.Membership as Membership

open import RoutingLib.Data.List
import RoutingLib.Data.List.Membership.DecSetoid as DecMembership
import RoutingLib.Data.List.Membership.Setoid.Properties as SetoidProperties

module RoutingLib.Data.List.Membership.DecSetoid.Properties where

  open SetoidProperties public
  
  module _ {c ℓ} (DS : DecSetoid c ℓ) where

    open DecSetoid DS renaming (Carrier to A; refl to ≈-refl; setoid to S)

    open Membership S using (_∈_)
    open DecMembership DS using (deduplicate)
 
    -- deduplicate

    ∈-deduplicate⁺ : ∀ {x xs} → x ∈ xs → x ∈ deduplicate xs
    ∈-deduplicate⁺ {y} {x ∷ xs} (here y≈x)   with any (x ≟_) xs
    ... | yes x∈xs = ∈-deduplicate⁺ (∈-resp-≈ S x∈xs (sym y≈x))
    ... | no  _    = here y≈x
    ∈-deduplicate⁺ {y} {x ∷ xs} (there y∈xs) with any (x ≟_) xs
    ... | yes _ = ∈-deduplicate⁺ y∈xs
    ... | no  _ = there (∈-deduplicate⁺ y∈xs)

    ∈-deduplicate⁻ : ∀ {x xs} → x ∈ deduplicate xs → x ∈ xs
    ∈-deduplicate⁻ {y} {[]} ()
    ∈-deduplicate⁻ {y} {x ∷ xs} x∈dedup with any (x ≟_) xs | x∈dedup
    ... | yes _ | x∈dedup[xs]       = there (∈-deduplicate⁻ x∈dedup[xs])
    ... | no  _ | here y≈x          = here y≈x
    ... | no  _ | there y∈dedup[xs] = there (∈-deduplicate⁻ y∈dedup[xs])
