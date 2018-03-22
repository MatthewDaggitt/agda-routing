open import Relation.Binary

module RoutingLib.Relation.Binary.Reasoning.PartialOrder
  {a ℓ₁ ℓ₂} (P : Poset a ℓ₁ ℓ₂) where

open import Data.Product using (proj₁)
import Relation.Binary.PreorderReasoning as PreR
import RoutingLib.Relation.Binary.NonStrictToStrict.PartialOrder as Strict

open Poset P
open Strict P using (_<_)

--------------------------------------------------------------------------------
-- Exports

open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)

_<⟨_⟩_ : ∀ x {y z} → x < y → y IsRelatedTo z → x IsRelatedTo z
_ <⟨ x<y ⟩ relTo y≤z = relTo (trans (proj₁ x<y) y≤z)
