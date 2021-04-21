open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra as Gamma_two_Algebra using (IsComposition)
  renaming (RouteMapMatrix to RouteMapMatrix')
import RoutingLib.Routing.Prelude as RoutingPrelude
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra; IsRoutingAlgebra)

module RoutingLib.lmv34.Asynchronous.Omega_two.Algebra
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (open RoutingPrelude algebra n)
  (A : AdjacencyMatrix)
  (Imp Prot Exp : RouteMapMatrix' isRoutingAlgebra n)
  (A=Imp∘Prot∘Exp : IsComposition isRoutingAlgebra n A Imp Prot Exp)
  where

open import Data.Fin using (Fin)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-step; ≤-trans)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Iteration.Asynchronous.Static.Schedule using (Schedule; 𝕋)
open import RoutingLib.Iteration.Asynchronous.Static.Schedule.Construct.Synchronous
open import RoutingLib.lmv34.Synchronous.Gamma_one.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two.Algebra isRoutingAlgebra n
open import RoutingLib.lmv34.Synchronous.Gamma_two.Properties isRoutingAlgebra A Imp Prot Exp A=Imp∘Prot∘Exp

open DecSetoid Γ₂-State-decSetoid using ()
  renaming (Carrier to Γ₂-State; _≈_ to _≈ₛ_)

--------------------------------------------------------------------------------
-- Operation definitions

-- Generalised (asynchronous) export function application
infix 10 _【_】'
_【_】' : RouteMapMatrix → (Fin n → Fin n → RoutingSet) → RoutingVector₂
(F 【 f 】') i q = (F i q) [ f q i ]

-- Generalised (asynchronous) operator
Γ₂,ₒ' : (Fin n → Fin n → RoutingSet) → RoutingVector₂
Γ₂,ₒ' f = Exp 【 f 】'

-- Generalised (asynchronous) RoutingVector application
infix 10 _||_||'
_||_||' : RouteMapMatrix → (Fin n → RoutingVector) → RoutingVector
(A || V ||' ) i = ⨁ₛ (λ q → (A i q) [ V i q ])

--------------------------------------------------------------------------------
-- State definitions

getV : Γ₂-State → RoutingVector
getV (V , I , O) = V

getI : Γ₂-State → RoutingVector₂
getI (V , I , O) = I

getO : Γ₂-State → RoutingVector₂
getO (V , I , O) = O

getV=V' : ∀ {S S'} → S ≈ₛ S' → getV S ≈ᵥ getV S'
getV=V' (V=V' , I=I' , O=O') = V=V'

getI=I' : ∀ {S S'} → S ≈ₛ S' → getI S ≈ᵥ,₂ getI S'
getI=I' (V=V' , I=I' , O=O') = I=I'

getO=O' : ∀ {S S'} → S ≈ₛ S' → getO S ≈ᵥ,₂ getO S'
getO=O' (V=V' , I=I' , O=O') = O=O'

--------------------------------------------------------------------------------
-- Schedule definitions

-- A triple schedule, one for each component V, I, O
Schedule₃ : ℕ → Set
Schedule₃ n = (Schedule n) × (Schedule n) × (Schedule n)

-- The synchronous schedule
ψ₃ˢʸⁿᶜ : Schedule₃ n
ψ₃ˢʸⁿᶜ = (ψˢʸⁿᶜ , ψˢʸⁿᶜ , ψˢʸⁿᶜ)

--------------------------------------------------------------------------------
-- Data history function

-- The function ϕ find the timestamp of the most recent data from node j
-- that is being used at node i.

module _ {n} (ψ : Schedule n) where
  open Schedule ψ
  
  ϕ : 𝕋 → Fin n → Fin n → 𝕋
  ϕ zero    i j = zero
  ϕ (suc t) i j with i ∈? α (suc t)
  ... | yes _ = β (suc t) i j
  ... | no  _ = ϕ t i j

  ϕ-causality : ∀ t i j → ϕ (suc t) i j ≤ t
  ϕ-causality zero    i j with i ∈? α (suc zero)
  ... | yes _ = β-causality zero i j
  ... | no  _ = ≤-refl
  ϕ-causality (suc t) i j with i ∈? α (suc (suc t))
  ... | yes _ = β-causality (suc t) i j
  ... | no  _ = ≤-step (ϕ-causality t i j)

  ϕ-decreasing : ∀ t i j → ϕ t i j ≤ t
  ϕ-decreasing zero    i j = ≤-refl
  ϕ-decreasing (suc t) i j = ≤-step (ϕ-causality t i j)

--------------------------------------------------------------------------------
-- Follow-cycle function

-- The function follow-cycle finds the timestamp of the most recent
-- data from the routing table V of node j, that is being used at
-- node i. It follows the cycle of data flow in Ω₂.

module _ {n} ((ψᵥ , ψᵢ , ψₒ) : Schedule₃ n) where
  tᵢ : 𝕋 → Fin n → 𝕋
  tᵢ t i = ϕ ψᵥ t i i

  tₒ : 𝕋 → Fin n → Fin n → 𝕋
  tₒ t i j = ϕ ψᵢ (tᵢ t i) i j

  tᵥ : 𝕋 → Fin n → Fin n → 𝕋
  tᵥ t i j = ϕ ψₒ (tₒ t i j) j j

  tᵢ≤t : ∀ t i → tᵢ (suc t) i ≤ t
  tᵢ≤t t i = ϕ-causality ψᵥ t i i

  tₒ≤t : ∀ t i j → tₒ (suc t) i j ≤ t
  tₒ≤t t i j = ≤-trans (ϕ-decreasing ψᵢ (tᵢ (suc t) i) i j) (tᵢ≤t t i) 

  tᵥ≤t : ∀ t i j → tᵥ (suc t) i j ≤ t
  tᵥ≤t t i j = ≤-trans (ϕ-decreasing ψₒ (tₒ (suc t) i j) j j) (tₒ≤t t i j)

follow-cycle : ∀ {n} → Schedule₃ n → 𝕋 → Fin n → Fin n → 𝕋
follow-cycle = tᵥ

follow-cycle-causality : ∀ {n} (ψ : Schedule₃ n) t i j → follow-cycle ψ (suc t) i j ≤ t
follow-cycle-causality = tᵥ≤t
