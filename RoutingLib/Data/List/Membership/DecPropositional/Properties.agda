open import Data.List.Any.Membership.Propositional using (_∈_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; decSetoid)

import RoutingLib.Data.List.Membership.DecPropositional as DecMembership
import RoutingLib.Data.List.Membership.DecSetoid.Properties as DSP
import RoutingLib.Data.List.Membership.Propositional.Properties as PropProperties

module RoutingLib.Data.List.Membership.DecPropositional.Properties where

  open PropProperties public
  
  module _ {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

    
    open DecMembership _≟_ using (deduplicate)
 
    -- deduplicate

    ∈-deduplicate⁺ : ∀ {x xs} → x ∈ xs → x ∈ deduplicate xs
    ∈-deduplicate⁺ = DSP.∈-deduplicate⁺ (decSetoid _≟_)

    ∈-deduplicate⁻ : ∀ {x xs} → x ∈ deduplicate xs → x ∈ xs
    ∈-deduplicate⁻ = DSP.∈-deduplicate⁻ (decSetoid _≟_)
