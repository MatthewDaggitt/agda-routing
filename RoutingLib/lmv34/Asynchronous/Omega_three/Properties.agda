open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition; RouteMapMatrix)

module RoutingLib.lmv34.Asynchronous.Omega_three.Properties
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra) {n}
  (A    : AdjacencyMatrix algebra n)
  (Imp Prot Exp : RouteMapMatrix isRoutingAlgebra n )
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_)
  renaming (proj₁ to π₁; proj₂ to π₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (DecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
open import RoutingLib.Iteration.Synchronous using (_^_)
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Algebra algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_zero.Properties algebra A
open import RoutingLib.lmv34.Asynchronous.Omega_one.Algebra isRoutingAlgebra A
open import RoutingLib.lmv34.Asynchronous.Omega_three isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp
open import RoutingLib.lmv34.Asynchronous.Omega_three.Algebra isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two.Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp
open import RoutingLib.lmv34.Synchronous.Gamma_three isRoutingAlgebra Imp Prot Exp
open import RoutingLib.lmv34.Synchronous.Gamma_three.Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp

open DecSetoid Γ₃-State-decSetoid using () renaming
  ( _≈_    to _≈ₛ_
  ; refl   to ≈ₛ-refl
  ; setoid to 𝕊ₛ
  )

--------------------------------------------------------------------------------
-- Proof that synchronous Ω₃ is indeed Γ₃

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
