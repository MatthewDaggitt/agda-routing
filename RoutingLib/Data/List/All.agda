open import Data.List.All
open import Data.Product using (_,_)
open import Relation.Unary using (_∩_; _⊆_)

module RoutingLib.Data.List.All where

  -- stdlib
  zip : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        All P ∩ All Q ⊆ All (P ∩ Q)
  zip ([] , [])             = []
  zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)
