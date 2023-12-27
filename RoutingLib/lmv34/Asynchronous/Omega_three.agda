open import RoutingLib.Routing.Prelude using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)

module RoutingLib.lmv34.Asynchronous.Omega_three
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where
  
open import Data.Nat using (zero; suc; s≤s;  _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (_×_; _,_)
  renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary using (DecSetoid)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n using (RoutingVector)
open import RoutingLib.lmv34.Synchronous.Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂-State)
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_three isRoutingAlgebra Imp Prot Exp
open import RoutingLib.lmv34.Synchronous.Gamma_three.Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_three.Algebra isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp

--------------------------------------------------------------------------------
-- Implementation of Ω₃

module _ ((ψᵥ , ψᵢ , ψₒ , ψₓ) : Schedule₄ n) where
  open Schedule ψᵥ renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule ψₒ renaming (α to αₒ; β to βₒ; β-causality to βₒ-causality)
  open Schedule ψₓ renaming (α to αₓ; β to βₓ; β-causality to βₓ-causality)
  
  Ω₃' : Γ₃-State → {t : 𝕋} → Acc _<_ t → Γ₃-State
  Ω₃' S {zero}  accₜ      = S
  Ω₃' S {suc t} (acc rec) =
    ( [ (Γ₃,ᵥ Iᵇ⁽ᵗ⁺¹⁾)                , Vᵗ ] αᵥ (suc t)
    , [ (Γ₃,ᵢ Iᵗ (∇ᵇ⁽ᵗ⁺¹⁾ , Δᵇ⁽ᵗ⁺¹⁾)) , Iᵗ ] αᵢ (suc t)
    , [ (Γ₃,ₒ Vᵇᵒ⁽ᵗ⁺̂¹⁾)               , Oᵗ ] αₒ (suc t)
    , [ π₁ (Γ₃,ₓ Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ Oᵇ⁽ᵗ⁺¹⁾)    , ∇ᵗ ] αₓ (suc t)
    , [ π₂ (Γ₃,ₓ Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ Oᵇ⁽ᵗ⁺¹⁾)    , Δᵗ ] αₓ (suc t)
    )
    where Vᵗ : RoutingVector
          Vᵗ = getV (Ω₃' S (rec ≤-refl))
          Vᵇᵒ⁽ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇᵒ⁽ᵗ⁺̂¹⁾ i = (getV (Ω₃' S (rec (s≤s (βₒ-causality t i i))))) i
          Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ i = (getV (Ω₃' S (rec (s≤s (βₓ-causality t i i))))) i
          Iᵗ : RoutingVector₂
          Iᵗ = getI (Ω₃' S (rec ≤-refl))
          Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₃' S (rec (s≤s (βᵥ-causality t i i))))) i j
          Oᵗ : RoutingVector₂
          Oᵗ = getO (Ω₃' S (rec ≤-refl))
          Oᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Oᵇ⁽ᵗ⁺¹⁾ i j = (getO (Ω₃' S (rec (s≤s (βₓ-causality t i i))))) i j
          ∇ᵗ : RoutingVector₂
          ∇ᵗ = get∇ (Ω₃' S (rec ≤-refl))
          Δᵗ : RoutingVector₂
          Δᵗ = getΔ (Ω₃' S (rec ≤-refl))
          ∇ᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          ∇ᵇ⁽ᵗ⁺¹⁾ i j = (get∇ (Ω₃' S (rec (s≤s (βₓ-causality t j i))))) i j
          Δᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Δᵇ⁽ᵗ⁺¹⁾ i j = (getΔ (Ω₃' S (rec (s≤s (βₓ-causality t j i))))) i j

Ω₃ : Schedule₄ n → Γ₃-State → 𝕋 → Γ₃-State
Ω₃ ψ S t = Ω₃' ψ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction/transformation Ω₃ → Ω₂

-- Transformation Ω₃ → Ω₂
Τ₃ : Γ₃-State → Γ₂-State
Τ₃ (V , I , O , (∇ , Δ)) = (V , I , O)
