

open import Relation.Binary using (Setoid)

open import RoutingLib.Function.Metric

module RoutingLib.Function.Metric.Properties {a ℓ} {S : Setoid a ℓ} (M : Metric S) where

  open Setoid S renaming (Carrier to A)
  open Metric M

