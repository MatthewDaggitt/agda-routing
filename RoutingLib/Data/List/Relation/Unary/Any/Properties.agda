
module RoutingLib.Data.List.Relation.Unary.Any.Properties where

open import Data.Fin using (Fin)
open import Data.List using (List; lookup; length)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; index)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

module _ {a p} {A : Set a} {P : Pred A p} where

  lookup-index : ∀ {xs} (p : Any P xs) → P (lookup xs (index p))
  lookup-index (here px)   = px
  lookup-index (there pxs) = lookup-index pxs
