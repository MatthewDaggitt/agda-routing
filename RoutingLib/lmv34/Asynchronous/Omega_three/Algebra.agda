open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)

module RoutingLib.lmv34.Asynchronous.Omega_three.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_three isRoutingAlgebra Imp Prot Exp

--------------------------------------------------------------------------------
-- State definitions

getV : Γ₃-State → RoutingVector
getV (V , I , O , (∇ , Δ)) = V

getI : Γ₃-State → RoutingVector₂
getI (V , I , O , (∇ , Δ)) = I

getO : Γ₃-State → RoutingVector₂
getO (V , I , O , (∇ , Δ)) = O

getD : Γ₃-State → RoutingVector₂ × RoutingVector₂
getD (V , I , O , (∇ , Δ)) = ∇ , Δ

get∇ : Γ₃-State → RoutingVector₂
get∇ (V , I , O , (∇ , Δ)) = ∇

getΔ : Γ₃-State → RoutingVector₂
getΔ (V , I , O , (∇ , Δ)) = Δ

--------------------------------------------------------------------------------
-- Schedule definitions

-- A quadriple schedule, one for each component V, I, O, (∇,Δ)
Schedule₄ : ℕ → Set
Schedule₄ n = (Schedule n) × (Schedule n) × (Schedule n) × (Schedule n)

ψ₄ˢʸⁿᶜ : Schedule₄ n
ψ₄ˢʸⁿᶜ = (ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ)
