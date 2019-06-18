
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Properties.RawRoutingAlgebra
  {a b ℓ} (𝔸 : RawRoutingAlgebra a b ℓ) where

open import Data.Nat using (zero; suc)
open import Level using (lift)
open RawRoutingAlgebra 𝔸

isLevelDistrib-cong : ∀ k {w x y z} → w ≈ x → y ≈ z →
                      Level_DistributiveIn[_,_]Alt 𝔸 k w y →
                      Level_DistributiveIn[_,_]Alt 𝔸 k x z
isLevelDistrib-cong zero    w≈x y≈z (lift x≈z) = lift (≈-trans (≈-trans (≈-sym w≈x) x≈z) y≈z)
isLevelDistrib-cong (suc k) w≈x y≈z distrib f x≤u u≤z x≤v v≤z =
  (distrib f
    (≤₊-respˡ-≈ (≈-sym w≈x) x≤u)
    (≤₊-respʳ-≈ (≈-sym y≈z) u≤z)
    (≤₊-respˡ-≈ (≈-sym w≈x) x≤v)
    (≤₊-respʳ-≈ (≈-sym y≈z) v≤z))
