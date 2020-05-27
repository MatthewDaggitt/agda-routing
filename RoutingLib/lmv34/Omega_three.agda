open import Algebra.Definitions
open import Data.Fin using (zero; suc; Fin)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _≤_;  _<_; _∸_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary using (DecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_one as Gamma_one
import RoutingLib.lmv34.Gamma_one.Algebra as Gamma_one_Algebra
open import RoutingLib.lmv34.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)
import RoutingLib.lmv34.Gamma_two as Gamma_two
import RoutingLib.lmv34.Gamma_two.Properties as Gamma_two_Properties
import RoutingLib.lmv34.Gamma_three as Gamma_three
import RoutingLib.lmv34.Gamma_three.Properties as Gamma_three_Properties
import RoutingLib.lmv34.Omega_zero as Omega_zero
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous using (αˢʸⁿᶜ; ψˢʸⁿᶜ)

module RoutingLib.lmv34.Omega_three
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open Gamma_one_Algebra isRoutingAlgebra n using (RoutingVector; ≈ᵥ-reflexive)
open Gamma_two isRoutingAlgebra Imp Prot Exp using (Γ₂-State)
open Gamma_two_Algebra isRoutingAlgebra n using (RoutingVector₂)
open Gamma_two_Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp using (≈ᵥ,₂-decSetoid)
open Gamma_three isRoutingAlgebra Imp Prot Exp using (Γ₃; Γ₃,ᵥ; Γ₃,ᵢ; Γ₃,ₒ; Γ₃,ₓ)
open Gamma_three_Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp using (Γ₃-State-decSetoid; Γ₃-cong)
open Omega_zero algebra A using ([_,_]_; [,]-⊤)
open DecSetoid Γ₃-State-decSetoid using () renaming (Carrier to Γ₃-State; _≈_ to _≈ₛ_ ; refl to ≈ₛ-refl; setoid to 𝕊ₛ)
open DecSetoid ≈ᵥ,₂-decSetoid using () renaming (reflexive to ≈ᵥ,₂-reflexive)

--------------------------------------------------------------------------------
-- Algebra

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
-- Implementation of Ω₃

-- A quadriple schedule, one for each component V, I, O, (∇,Δ)
Schedule₄ : ℕ → Set
Schedule₄ n = (Schedule n) × (Schedule n) × (Schedule n) × (Schedule n)

module _ ((ψᵥ , ψᵢ , ψₒ , ψₓ) : Schedule₄ n) where
  open Schedule ψᵥ renaming (α to αᵥ; β to βᵥ; β-causality to βᵥ-causality)
  open Schedule ψᵢ renaming (α to αᵢ; β to βᵢ; β-causality to βᵢ-causality)
  open Schedule ψₒ renaming (α to αₒ; β to βₒ; β-causality to βₒ-causality)
  open Schedule ψₓ renaming (α to αₓ; β to βₓ; β-causality to βₓ-causality)
  
  Ω₃' : Γ₃-State → {t : 𝕋} → Acc _<_ t → Γ₃-State
  Ω₃' S {zero}  accₜ      = S
  Ω₃' S {suc t} (acc rec) =
    ( [ (Γ₃,ᵥ Iᵇ⁽ᵗ⁺¹⁾)               , Vᵗ ] αᵥ (suc t)
    , [ (Γ₃,ᵢ Iᵗ (∇ᵇ⁽ᵗ⁺¹⁾ , Δᵇ⁽ᵗ⁺¹⁾)) , Iᵗ ] αᵢ (suc t)
    , [ (Γ₃,ₒ Vᵇᵒ⁽ᵗ⁺̂¹⁾)              , Oᵗ ] αₒ (suc t)
    , [ π₁ (Γ₃,ₓ Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ Oᵇ⁽ᵗ⁺¹⁾)    , ∇ᵗ ] αₓ (suc t)
    , [ π₂ (Γ₃,ₓ Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ Oᵇ⁽ᵗ⁺¹⁾)    , Δᵗ ] αₓ (suc t)
    )
    where Vᵗ : RoutingVector
          Vᵗ = getV (Ω₃' S (rec t ≤-refl))
          Vᵇᵒ⁽ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇᵒ⁽ᵗ⁺̂¹⁾ i = (getV (Ω₃' S (rec (βₒ (suc t) i i) (s≤s (βₒ-causality t i i))))) i
          Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ : RoutingVector
          Vᵇᵈ⁽̂ᵗ⁺̂¹⁾ i = (getV (Ω₃' S (rec (βₓ (suc t) i i) (s≤s (βₓ-causality t i i))))) i
          Iᵗ : RoutingVector₂
          Iᵗ = getI (Ω₃' S (rec t ≤-refl))
          Iᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Iᵇ⁽ᵗ⁺¹⁾ i j = (getI (Ω₃' S (rec (βᵥ (suc t) i i) (s≤s (βᵥ-causality t i i))))) i j
          Oᵗ : RoutingVector₂
          Oᵗ = getO (Ω₃' S (rec t ≤-refl))
          Oᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Oᵇ⁽ᵗ⁺¹⁾ i j = (getO (Ω₃' S (rec (βₓ (suc t) i i) (s≤s (βₓ-causality t i i))))) i j
          ∇ᵗ : RoutingVector₂
          ∇ᵗ = get∇ (Ω₃' S (rec t ≤-refl))
          Δᵗ : RoutingVector₂
          Δᵗ = getΔ (Ω₃' S (rec t ≤-refl))
          ∇ᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          ∇ᵇ⁽ᵗ⁺¹⁾ i j = (get∇ (Ω₃' S (rec (βₓ (suc t) j i) (s≤s (βₓ-causality t j i))))) i j
          Δᵇ⁽ᵗ⁺¹⁾ : RoutingVector₂
          Δᵇ⁽ᵗ⁺¹⁾ i j = (getΔ (Ω₃' S (rec (βₓ (suc t) j i) (s≤s (βₓ-causality t j i))))) i j

Ω₃ : Schedule₄ n → Γ₃-State → 𝕋 → Γ₃-State
Ω₃ ψ S t = Ω₃' ψ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Proof that synchronous Ω₃ is indeed Γ₃

ψ₄ˢʸⁿᶜ : Schedule₄ n
ψ₄ˢʸⁿᶜ = (ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ)

Ω₃'ˢʸⁿᶜ=Γ₃ : ∀ S {t} (accₜ : Acc _<_ t) →  Ω₃' ψ₄ˢʸⁿᶜ S accₜ ≈ₛ (Γ₃ ^ t) S
Ω₃'ˢʸⁿᶜ=Γ₃ S {zero}  accₜ      = ≈ₛ-refl
Ω₃'ˢʸⁿᶜ=Γ₃ S {suc t} (acc rec) = begin
  Ω₃' ψ₄ˢʸⁿᶜ S (acc rec)                                ≡⟨⟩
  ([ Γ₃,ᵥ I[t]               , V[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ Γ₃,ᵢ I[t] (∇[t] , Δ[t]) , I[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ Γ₃,ₒ V[t]               , O[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ (π₁ (Γ₃,ₓ V[t] O[t]))   , ∇[t] ] αˢʸⁿᶜ (suc t)) ,
  ([ (π₂ (Γ₃,ₓ V[t] O[t]))   , Δ[t] ] αˢʸⁿᶜ (suc t))    ≈⟨ ≈ᵥ-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ , ≈ᵥ,₂-reflexive [,]-⊤ ⟩
  (Γ₃,ᵥ I[t]) ,
  (Γ₃,ᵢ I[t] (∇[t] , Δ[t])) ,
  (Γ₃,ₒ V[t]) ,
  (Γ₃,ₓ V[t] O[t])                                      ≡⟨⟩
  Γ₃ (V[t] , I[t] , O[t] , ∇[t] , Δ[t])                 ≈⟨ Γ₃-cong (Ω₃'ˢʸⁿᶜ=Γ₃ S (rec t ≤-refl)) ⟩
  (Γ₃ ^ (suc t)) S                                      ∎
  where open EqReasoning 𝕊ₛ
        V[t] : RoutingVector
        V[t] = getV (Ω₃' ψ₄ˢʸⁿᶜ S (rec t ≤-refl))
        I[t] : RoutingVector₂
        I[t] = getI (Ω₃' ψ₄ˢʸⁿᶜ S (rec t ≤-refl))
        O[t] : RoutingVector₂
        O[t] = getO (Ω₃' ψ₄ˢʸⁿᶜ S (rec t ≤-refl))
        ∇[t] : RoutingVector₂
        ∇[t] = get∇ (Ω₃' ψ₄ˢʸⁿᶜ S (rec t ≤-refl))
        Δ[t] : RoutingVector₂
        Δ[t] = getΔ (Ω₃' ψ₄ˢʸⁿᶜ S (rec t ≤-refl))

Ω₃ˢʸⁿᶜ=Γ₃ : ∀ S t → Ω₃ ψ₄ˢʸⁿᶜ S t ≈ₛ (Γ₃ ^ t) S
Ω₃ˢʸⁿᶜ=Γ₃ S t = Ω₃'ˢʸⁿᶜ=Γ₃ S (<-wellFounded t)

--------------------------------------------------------------------------------
-- Reduction Ω₃ → Ω₂

Τ₃ : Γ₃-State → Γ₂-State
Τ₃ (V , I , O , (∇ , Δ)) = (V , I , O)
