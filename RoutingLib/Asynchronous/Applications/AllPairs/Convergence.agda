open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; ∃; _,_; proj₁; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Unary using (U; U-Universal)

open import RoutingLib.Asynchronous using (Parallelisation)
import RoutingLib.Asynchronous.Applications.AllPairs as AllPairs
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Table using (min∞)
open import RoutingLib.Data.Table.All using (All)
open import RoutingLib.Data.Table.Any using (Any)
open import RoutingLib.Data.Table.Properties using (min∞[s]≤min∞[t]; min∞[t]≤x)

module RoutingLib.Asynchronous.Applications.AllPairs.Convergence {n}(𝕤 : Schedule n)(x₀ : AllPairs.Matrix n)(Cᵢ,ᵢ : ∀ i → x₀ i i ≡ N 0) where

  
  open AllPairs n hiding (f)
  open import RoutingLib.Asynchronous.Applications.AllPairs.Properties n
  open Schedule 𝕤
  open Parallelisation all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Propositions.UresinDubois3 all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Theorems.UresinDubois1 𝕤 all-pairs-parallelisation
  
  D₀ : MPred
  D₀ i = U

  x₀∈D₀ : x₀ ∈ D₀
  x₀∈D₀ i = U-Universal (x₀ i)

  D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀
  D₀-subst {_} {y} _ _ i = U-Universal (y i)

  closed : ∀ x → x ∈ D₀ → f x ∈ D₀
  closed x _ i = U-Universal (f x i)

  f-monotone : ∀ {x y} → x ∈ D₀ × y ∈ D₀ → (∀ i → x i ≼ y i) → ∀ i → f x i ≼ f y i
  f-monotone {x} {y} ∈D x≼y i j = min∞[s]≤min∞[t] (x i j) (inj₁ (x≼y i j)) ≤-path-cost
      where
      ≤-path-cost : ∀ k → x i j ≤ path-cost y i j k ⊎
                           Σ (Fin n) (λ v → path-cost x i j v ≤ path-cost y i j k)
      ≤-path-cost k = inj₂ (k , path-cost-monotone x≼y i j k)

  iter-dec : ∀ K → iter x₀ (suc K) ≼ₘ iter x₀ K
  iter-dec zero i j = min∞[t]≤x (x₀ i j) (path-cost x₀ i j) (inj₁ ≤-refl)
  iter-dec (suc K) i = f-monotone
           ((λ l → U-Universal (iter x₀ (suc K))) , λ l → U-Universal (iter x₀ K))
           (λ j → iter-dec K j) i

  iter-converge : ∃ λ T → (∀ t → iter x₀ T ≈ iter x₀ (T +ℕ t)) ×
                                (∀ {t} → t <ℕ T → iter x₀ t ≉ iter x₀ (suc t))
  iter-converge = {!!}

  open proof x₀ D₀ x₀∈D₀ D₀-subst _≼_ ≼-refl ≼-reflexive ≼-antisym ≼-trans closed f-monotone iter-dec iter-converge hiding (ξ)

  open Theorem1 aco x₀∈D0

  converging-time : 𝕋
  converging-time = proj₁ theorem1

  converging-state : Matrix
  converging-state = ξ
