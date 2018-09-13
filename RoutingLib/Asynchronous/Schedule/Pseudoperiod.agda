open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _≤_; _∸_; _≟_; _⊔_; _+_)
open import Data.Nat.Properties using (1+n≰n; ≤-refl; ≤+≢⇒<; <⇒≤; +-suc)
open import Function using (_∘_)
open import Data.List using (foldr; tabulate; applyUpTo)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (_∈_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.Table using (max)
import RoutingLib.Data.List.Extrema.Nat as List

module RoutingLib.Asynchronous.Schedule.Pseudoperiod {i ℓ} {I : Set i} (𝕤 : Schedule I ℓ) where

open Schedule 𝕤

-----------------
-- Activations --
-----------------

-- return the first time after t but before t + suc k that i is active
nextActive' : (t k : 𝕋) {i : I} → i ∈ α (t + suc k) → Acc _<_ k → 𝕋
nextActive' t zero    {i} _          _       = suc t
nextActive' t (suc k) {i} i∈α[t+1+K] (acc rs) with i ∈?α t
... | yes i∈α                         = t
... | no  i∉α rewrite +-suc t (suc k) = nextActive' (suc t) k i∈α[t+1+K] (rs k ≤-refl)

-- returns the first time after t in which that i is active
nextActive : 𝕋 → I → 𝕋
nextActive t i with nonstarvation t i
... | (K , i∈α[t+1+K]) = nextActive' t K i∈α[t+1+K] (<-wellFounded K)

-- returns the first time after t such that all nodes have activated since t
allActive : 𝕋 → 𝕋
allActive t = max t (nextActive t)

---------------
-- Data flow --
---------------

-- pointExpiryᵢⱼ returns a time such that i does not use data from j from time t

pointExpiryᵢⱼ : I → I → 𝕋 → 𝕋
pointExpiryᵢⱼ i j t = proj₁ (finite t i j)

-- expiryᵢⱼ returns a time such that i only uses data from j after time t

expiryᵢⱼ : 𝕋 → I → I → 𝕋
expiryᵢⱼ t i j = List.max t (applyUpTo (pointExpiryᵢⱼ i j) (suc t))

-- expiryᵢⱼ : 𝕋 → Fin n → Fin n → 𝕋
-- expiryᵢⱼ t i j = max {suc t} t (pointExpiryᵢⱼ i j)


-- expiryᵢ returns a time ≥ t such that i only ever uses data from after time t
expiryᵢ : 𝕋 → I → 𝕋
expiryᵢ t i = max t (expiryᵢⱼ t i)

-- expiry returns a time ≥ t such that all nodes only ever uses data from after time t
expiry : 𝕋 → 𝕋
expiry t = max t (expiryᵢ t)

-------------------
-- Pseudo-Cycles --
-------------------

-- Definition of φ
φ : ℕ → 𝕋
φ zero     = zero
φ (suc K)  = suc (expiry (allActive (φ K)))

-- Definition of τ
τ : ℕ → I → 𝕋
τ K i = nextActive (φ K) i
