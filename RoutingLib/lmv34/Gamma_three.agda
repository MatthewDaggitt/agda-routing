open import Algebra.Core using (Op₂)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)

open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
import RoutingLib.lmv34.Gamma_two as Gamma_two using (Γ₂,ᵥ; Γ₂,ᵢ; Γ₂,ₒ)
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (RouteMapMatrix)
import RoutingLib.lmv34.Gamma_three.Algebra as Gamma_three_Algebra

module RoutingLib.lmv34.Gamma_three
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  where

open Gamma_one_Algebra isRoutingAlgebra n
open Gamma_two_Algebra isRoutingAlgebra n 
open Gamma_three_Algebra isRoutingAlgebra n 
open Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂,ᵥ; Γ₂,ᵢ; Γ₂,ₒ)
------------------------------------
-- State model

record Γ₃-State : Set a where
  constructor S₃
  field
    V : RoutingVector
    I : RoutingVector₂
    O : RoutingVector₂
    ∇,Δ : RoutingVector₂ × RoutingVector₂

------------------------------------
-- Computation Model

Γ₃,ᵥ : RoutingVector₂ →  RoutingVector
Γ₃,ᵥ = Γ₂,ᵥ 

Γ₃,ᵢ : RoutingVector₂ → (RoutingVector₂ × RoutingVector₂) → RoutingVector₂
Γ₃,ᵢ I  (∇ , Δ) = (I -ᵥ (Γ₂,ᵢ ∇)) ∪ᵥ (Γ₂,ᵢ Δ)

Γ₃,ₒ : RoutingVector → RoutingVector₂
Γ₃,ₒ = Γ₂,ₒ

Γ₃,ₓ : RoutingVector → RoutingVector₂ → RoutingVector₂ × RoutingVector₂
Γ₃,ₓ V O = diffᵥ O (Γ₃,ₒ V)

Γ₃ : Γ₃-State → Γ₃-State
Γ₃ (S₃ V I O (∇ , Δ)) = S₃ (Γ₃,ᵥ I) (Γ₃,ᵢ I (∇ , Δ)) (Γ₃,ₒ V) (Γ₃,ₓ V O)
