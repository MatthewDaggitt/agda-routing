open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ∁)
open import Relation.Binary as B using (_⇒_)
open import Relation.Binary.Indexed.Homogeneous
open import Relation.Nullary using (Dec; yes; no)

open import RoutingLib.Relation.Unary using (Finite)

import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FinSubset
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as Eq

module RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality
  {n a ℓ} (S : IndexedDecSetoid (Fin n) a ℓ) where

open IndexedDecSetoid S using (indexedSetoid; _≟ᵢ_; _≈ᵢ_) renaming ( Carrierᵢ to Aᵢ )

--------------------------------------------------------------------------------
-- Re-export contents of equality

open Eq indexedSetoid public

--------------------------------------------------------------------------------
-- Extra decidability properties

_≟[_]_ : ∀ x p y → Dec (x ≈[ p ] y)
x ≟[ p ] y = FinSubset.dec Aᵢ _≈ᵢ_ _≟ᵢ_ x y

module _ (p : Subset n) where

  ≈ₛ-isDecEquivalence : B.IsDecEquivalence _≈[ p ]_
  ≈ₛ-isDecEquivalence = record
    { isEquivalence = ≈ₛ-isEquivalence p
    ; _≟_           = _≟[ p ]_
    }

  ≈ₛ-decSetoid : B.DecSetoid _ _
  ≈ₛ-decSetoid = record
    { isDecEquivalence = ≈ₛ-isDecEquivalence
    }
