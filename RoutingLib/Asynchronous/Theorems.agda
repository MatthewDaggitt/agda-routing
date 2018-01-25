
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; _≤_; z≤n; zero; suc)
open import Data.Nat.Properties using (≰⇒>; module ≤-Reasoning; ≤-decTotalOrder; ≤-refl; ≤-trans; <⇒≤; <-irrefl; <-transˡ; <-asym; <⇒≱; ≮⇒≥)
open import Data.Fin using (Fin; pred; fromℕ; inject₁) renaming (_<_ to _<𝔽_; _≤_ to _≤𝔽_; _≤?_ to _≤𝔽?_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_) renaming (_<?_ to _<𝔽?_)
open import Data.Product using (∃; _×_; _,_; proj₂)
open import Data.List using (List; length)
open import Data.Vec using (Vec; lookup; fromList) renaming (_∈_ to _∈ᵥ_)
open import Data.Vec.Properties using (List-∈⇒∈)
open import Relation.Binary using (Setoid; Decidable; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Asynchronous
open import RoutingLib.Relation.Unary using () renaming (_⊈_ to _⊈ᵤ_)
open import RoutingLib.Data.Nat.Properties using (n≤0⇒n≡0; ℕₛ)
open import RoutingLib.Data.Fin.Properties using (≤fromℕ; ≤+≢⇒<; <⇒≤pred)
open import RoutingLib.Data.List.All using (AllPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-length)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (sort; sort-Sorted; sort-↗)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-unique; ↗-length; ↗-∈ˡ; ↗-∈ʳ)
open import RoutingLib.Data.List.Sorting.Nat using (strictlySorted)
open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Vec.Properties using (∈-lookup; ∈-fromList⁻; ∈-lookup⁺)
open import RoutingLib.Data.Vec.All.Properties using (AllPairs-lookup; AllPairs-fromList⁺)
open import RoutingLib.Function.Image using (FiniteImage)

module RoutingLib.Asynchronous.Theorems {a ℓ n} {S : Table (Setoid a ℓ) n}
                                        {P : Parallelisation S} where

  -- Export core publically
  
  open import RoutingLib.Asynchronous.Theorems.Core public

  -- Theorems
  
  totalACO⇒safe : ∀ {p} → TotalACO P p → IsAsynchronouslySafe P
  totalACO⇒safe = isAsynchronouslySafe
    where open import RoutingLib.Asynchronous.Theorems.UresinDubois1 P using (isAsynchronouslySafe)

  ultra⇒totalACO : UltrametricConditions P → TotalACO P _
  ultra⇒totalACO ultra = totalACO
    where open import RoutingLib.Asynchronous.Theorems.MetricToBox ultra using (totalACO)

  ultra⇒safe : UltrametricConditions P → IsAsynchronouslySafe P
  ultra⇒safe ultra = totalACO⇒safe (ultra⇒totalACO ultra)
