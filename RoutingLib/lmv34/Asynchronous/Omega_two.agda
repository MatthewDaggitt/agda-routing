open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)

module RoutingLib.lmv34.Asynchronous.Omega_two
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (zero; suc; s≤s; _<_; _≤_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_two.Algebra isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp
open import RoutingLib.lmv34.Synchronous.Gamma_one isRoutingAlgebra A
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two isRoutingAlgebra Imp Prot Exp
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra isRoutingAlgebra n

--------------------------------------------------------------------------------
-- Implementation of Ω₂

module _ ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n) where
  open Schedule ψᵥ renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule ψₒ renaming (α to αₒ; β to βₒ; β-causality to βₒ-causality)
  
  Ω₂' : Γ₂-State → {t : 𝕋} → Acc _<_ t → Γ₂-State
  Ω₂' S {zero}  accₜ      = S
  Ω₂' S {suc t} (acc rec) =
    ( [ Γ₂,ᵥ Iᵇ⁽ᵗ⁺¹⁾ , Vᵗ ] αᵥ (suc t)
    , [ Γ₂,ᵢ Oᵇ⁽ᵗ⁺¹⁾ , Iᵗ ] αᵢ (suc t)
    , [ Γ₂,ₒ Vᵇ⁽ᵗ⁺̂¹⁾ , Oᵗ ] αₒ (suc t)
    )
    where Vᵗ : RoutingVector
          Vᵗ = getV (Ω₂' S (rec t ≤-refl))
          Vᵇ⁽ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇ⁽ᵗ⁺̂¹⁾ i = (getV (Ω₂' S (rec (βₒ (suc t) i i) (s≤s (βₒ-causality t i i))))) i
          Iᵗ : RoutingVector₂
          Iᵗ = getI (Ω₂' S (rec t ≤-refl))
          Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₂' S (rec (βᵥ (suc t) i i) (s≤s (βᵥ-causality t i i))))) i j
          Oᵗ : RoutingVector₂
          Oᵗ = getO (Ω₂' S (rec t ≤-refl))
          Oᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Oᵇ⁽ᵗ⁺¹⁾ i j = (getO (Ω₂' S (rec (βᵢ (suc t) j i) (s≤s (βᵢ-causality t j i))))) i j

Ω₂ : Schedule₃ n → Γ₂-State → 𝕋 → Γ₂-State
Ω₂ ψ S t = Ω₂' ψ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction/transformation Ω₂ → Ω₁

-- Transformation Ω₂ → Ω₁
Τ₂ : Γ₂-State → Γ₁-State
Τ₂ (V , I , O) = V

-- Schedule reduction Ω₂ → Ω₁
r₂ : Schedule₃ n → Schedule n
r₂ (ψᵥ , ψᵢ , ψₒ) = record { α = α' ; β = β' ; β-causality = β'-causality}
  where open Schedule ψᵥ using () renaming (α to αᵥ)
        α' : 𝕋 → Subset n
        α' = αᵥ
        β' : 𝕋 → Fin n → Fin n → 𝕋
        β' = follow-cycle (ψᵥ , ψᵢ , ψₒ)
        β'-causality : ∀ t i j → β' (suc t) i j ≤ t
        β'-causality = follow-cycle-causality (ψᵥ , ψᵢ , ψₒ)
