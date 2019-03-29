open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (AdjacencyMatrixᵀ)

module RoutingLib.lmv34.Gamma_two
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (ImpProt : AdjacencyMatrix algebra n)
  (Exp : AdjacencyMatrixᵀ isRoutingAlgebra n)
  where

open Routing algebra n renaming (I to M)
open RawRoutingAlgebra algebra
open Gamma_one_Algebra isRoutingAlgebra n using (RoutingVector; _⊕ᵥ_; ~_)
open Gamma_two_Algebra isRoutingAlgebra n

------------------------------------
-- State model

record Γ₂-State : Set a where
  field
    V : RoutingVector
    I : RoutingVector₂
    O : RoutingVector₂

------------------------------------
-- Computation Model

Γ₂,ᵥ : RoutingVector₂ → RoutingVector
Γ₂,ᵥ I = I ↓ ⊕ᵥ ~ M

Γ₂,ᵢ : RoutingVector₂ → RoutingVector₂
Γ₂,ᵢ O = ImpProt 〖 O 〗

Γ₂,ₒ : RoutingVector → RoutingVector₂
Γ₂,ₒ V = Exp 【 V 】

Γ₂-Model : Γ₂-State → Γ₂-State
Γ₂-Model State = record { V = Γ₂,ᵥ (Γ₂-State.I State);
                          I = Γ₂,ᵢ (Γ₂-State.O State);
                          O = Γ₂,ₒ (Γ₂-State.V State) }
