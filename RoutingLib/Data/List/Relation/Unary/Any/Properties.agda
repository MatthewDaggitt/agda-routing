open import Data.List using (List; lookup; length)
open import Data.List.Any as Any using (Any; here; there; index)
open import Data.Fin using (Fin)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

module RoutingLib.Data.List.Relation.Unary.Any.Properties where

module _ {a p} {A : Set a} {P : Pred A p} where

  lookup-index : ∀ {xs} (p : Any P xs) → P (lookup xs (index p))
  lookup-index (here px)   = px
  lookup-index (there pxs) = lookup-index pxs
