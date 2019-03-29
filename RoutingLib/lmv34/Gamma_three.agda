open import Data.Product using (_×_; _,_)

open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_two as Gamma_two
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (AdjacencyMatrixᵀ)
import RoutingLib.lmv34.Gamma_three.Algebra as Gamma_three_Algebra

module RoutingLib.lmv34.Gamma_three
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (ImpProt : AdjacencyMatrix algebra n)
  (Exp : AdjacencyMatrixᵀ isRoutingAlgebra n)
  where

open Gamma_one_Algebra isRoutingAlgebra n
open Gamma_two isRoutingAlgebra ImpProt Exp
open Gamma_two_Algebra isRoutingAlgebra n
open Gamma_three_Algebra isRoutingAlgebra n

------------------------------------
-- State model

record Γ₃-State : Set a where
  field
    V : RoutingVector
    I : RoutingVector₂
    O : RoutingVector₂
    ∇ : RoutingVector₂
    Δ : RoutingVector₂

------------------------------------
-- Computation Model
Γ₃,ᵥ : RoutingVector₂ →  RoutingVector
Γ₃,ᵥ = Γ₂,ᵥ

Γ₃,ᵢ : RoutingVector₂ × (RoutingVector₂ × RoutingVector₂) → RoutingVector₂
Γ₃,ᵢ (I , (∇ , Δ)) = (I -ᵥ (Γ₂,ᵢ ∇)) ∪ᵥ (Γ₂,ᵢ Δ)

Γ₃,ₒ : RoutingVector → RoutingVector₂
Γ₃,ₒ = Γ₂,ₒ

Γ₃,ₓ : RoutingVector → RoutingVector₂ → RoutingVector₂ × RoutingVector₂
Γ₃,ₓ V O = diffᵥ O (Γ₃,ₒ V)
