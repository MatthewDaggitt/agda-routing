open import Level using (Level; _⊔_; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; _≤_; z≤n; zero; suc; ≤-pred)
open import Data.Nat.Properties using (≰⇒>; module ≤-Reasoning; ≤-decTotalOrder; ≤-refl; ≤-trans; <⇒≤; <-irrefl; <-transˡ; <-asym; <⇒≱; ≮⇒≥; _<?_; m+n≮n; n≤1+n)
open import Data.Fin using (Fin; pred; fromℕ; fromℕ≤; inject₁) renaming (_<_ to _<𝔽_; _≤_ to _≤𝔽_; _≤?_ to _≤𝔽?_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (reverse) renaming (_≟_ to _≟𝔽_) renaming (_<?_ to _<𝔽?_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; length)
open import Data.Vec using (Vec; lookup; fromList) renaming (_∈_ to _∈ᵥ_)
open import Data.Vec.Properties using (List-∈⇒∈)
open import Relation.Binary using (Setoid; Decidable; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (U)
open import Function using (_∘_)

open import RoutingLib.Asynchronous
open import RoutingLib.Relation.Unary using () renaming (_⊂_ to _⊂ᵤ_; _⊈_ to _⊈ᵤ_)
open import RoutingLib.Data.Nat.Properties using (n≤0⇒n≡0; m+n≮m; ℕₛ)
open import RoutingLib.Data.Fin.Properties using (≤fromℕ; ≤+≢⇒<; <⇒≤pred)
open import RoutingLib.Data.List.All using (AllPairs)
open import RoutingLib.Data.List using (max)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-length)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (sort; sort-Sorted; sort-↗)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-unique; ↗-length; ↗-∈ˡ; ↗-∈ʳ)
open import RoutingLib.Data.List.Sorting.Nat using (strictlySorted)
--open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.Vec.Properties using (∈-lookup; ∈-fromList⁻; ∈-lookup⁺)
open import RoutingLib.Data.Vec.All.Properties using (AllPairs-lookup; AllPairs-fromList⁺)
open import RoutingLib.Function.Image using (FiniteImage)
open import RoutingLib.Asynchronous.Theorems using (ACO; ACO₂)

module RoutingLib.Asynchronous.Theorems.ACO1ToACO2
  {a ℓ n} {S : Table (Setoid a ℓ) n} {P : Parallelisation S} {p} (aco₂ : ACO₂ P p) where

  open Parallelisation P
  open ACO₂ aco₂ using () renaming
    ( T           to T'
    ; D           to D'
    ; D-finish    to D'-finish
    ; D-subst     to D-subst'
    ; f-monotonic to f-monotonic'
    )

  record ⊤ : Set p where


  -- Finish time
  
  T : ℕ
  T = suc T'

  -- Sets
  
  D : ℕ → Pred p
  D K with K <? T
  ... | yes K<T = D' (fromℕ≤ K<T)
  ... | no  _   = D' (fromℕ T')

  -- The boxes decrease in size
  
  D-decreasing : ∀ K → K < T → D (suc K) ⊂ D K
  D-decreasing K K<T'  with K <? T | suc K <? T
  ... | yes K<T | yes 1+K<T = D₁₊ₖ⊆Dₖ , {!!} , {!!} , {!!}
    where
    D₁₊ₖ⊆Dₖ : D' (fromℕ≤ 1+K<T) ⊆ D' (fromℕ≤ K<T)
    D₁₊ₖ⊆Dₖ = {!proj₁ (D-decreasing (fromℕ≤ 1+K<T) ?)!}
    --x∈Dₖ : x ∈ D' 1+K<T

  ... | yes _   | no  1+K≮T = {!!}
  ... | no  K≮T | _         = contradiction K<T' K≮T
    
  -- Fixed point

  ξ : M
  ξ = proj₁ D'-finish

  ξ-singleton : ∀ K → Singleton-t ξ (D (T + K))
  ξ-singleton K with (T + K) <? T
  ... | yes T+K<T = contradiction T+K<T (m+n≮m T K)
  ... | no  _     = proj₂ D'-finish
    
  D-finish : ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
  D-finish = ξ , ξ-singleton

  -- Monotonicity
  
  f-monotonic : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
  f-monotonic K {t} t∈Dₖ with K <? T | suc K <? T
  ... | yes K<T | yes 1+K<T = {!!} --subst (λ v → f t ∈ D v) {x = {!!}} {!!} (f-monotonic' (fromℕ≤ K<T) t∈Dₖ)
  ... | yes K<T | no  1+K≮T = {!f-monotonic'!}
  ... | no  K≮T | yes 1+K<T = contradiction (≤-trans (n≤1+n _) 1+K<T) K≮T
  ... | no  K≮T | no  1+K≮T = {!!} --f-monotonic' t∈Dₖ
  
  D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
  D-subst K x≈y x∈Dₖ with K <? T
  ... | yes K<T = D-subst' (fromℕ≤ K<T) x≈y x∈Dₖ
  ... | no  _   = D-subst' (fromℕ T') x≈y x∈Dₖ
  
  aco₁ : ACO P p
  aco₁ = record
    { T            = T
    ; D            = D
    ; D-decreasing = D-decreasing
    ; D-finish     = D-finish
    ; f-monotonic  = f-monotonic
    ; D-subst      = D-subst
    }
