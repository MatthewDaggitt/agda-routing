
module RoutingLib.Relation.Nullary.Construct.Add.Point
  {a} (A : Set a) where

data Pointed : Set a where
  ∙   : Pointed
  [_] : A → Pointed
