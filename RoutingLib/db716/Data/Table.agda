open import RoutingLib.Data.Table
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

module RoutingLib.db716.Data.Table where
  
  tail : ∀ {a n} {A : Set a} → Table A (suc n) → Table A n
  tail v = λ i → v (suc i)
