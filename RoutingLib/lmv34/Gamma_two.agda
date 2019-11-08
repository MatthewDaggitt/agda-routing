open import Algebra.FunctionProperties.Core using (Op₂)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (RouteMapMatrix; IsComposition)

module RoutingLib.lmv34.Gamma_two
  {a b ℓ} {n : ℕ}
  {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  where

open Routing algebra n renaming (I to M)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingVector; _⊕ᵥ_; ~_;_≈ᵥ_)
open Gamma_two_Algebra isRoutingAlgebra n

------------------------------------
-- State model

record Γ₂-State : Set a where
  constructor S₂
  field
    V : RoutingVector
    I : RoutingVector₂
    O : RoutingVector₂

------------------------------------
-- Computation Model

Γ₂,ᵥ : RoutingVector₂ → RoutingVector
Γ₂,ᵥ I = I ↓ ⊕ᵥ ~ M

Γ₂,ᵢ : RoutingVector₂ → RoutingVector₂
Γ₂,ᵢ O = (Imp ●ₘ Prot) 〖 O 〗

Γ₂,ₒ : RoutingVector → RoutingVector₂
Γ₂,ₒ V = Exp 【 V 】

Γ₂ : Γ₂-State → Γ₂-State
Γ₂ (S₂ V I O) = S₂ (Γ₂,ᵥ I) (Γ₂,ᵢ O) (Γ₂,ₒ V)
