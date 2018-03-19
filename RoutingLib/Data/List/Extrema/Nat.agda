open import Data.Nat using (ℕ)
open import Data.Nat.Properties

import RoutingLib.Data.List.Extrema as Extrema

module RoutingLib.Data.List.Extrema.Nat where

  open Extrema ≤-totalOrder public
    using
    ( argmin; argmax; min; max
    ; argmin-sel; argmin-max
    )

  
