open import Data.List using (List; length; []; _∷_; filter)
open import Data.List.Any as Any using (Any; here; there)
import Data.List.Membership.Setoid as Membership
import Data.List.Relation.Sublist.Setoid as Sublist
open import Data.List.Membership.Setoid.Properties using (∈-filter⁻; ∈-filter⁺; ∈-resp-≈)
open import Data.List.Properties using (length-filter; filter-notAll)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; ≤-trans; ≤-step; m≤m+n; ≤-reflexive; pred-mono; ≤+≢⇒<; ≤-refl; <⇒≤)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Function using (_∘_)
open import Relation.Binary using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; _⇒_; Decidable)
open import Relation.Binary.PropositionalEquality using (subst; cong; _≡_; trans; sym; refl)
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary.Properties using (∁?)
open import Induction.Nat using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Data.Table using (Table)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Convergence.Conditions
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3 as Prop3

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois4
  {a ℓ n p}
  {𝕊ᵢ : Table (Setoid a ℓ) n}
  (𝓟 : Parallelisation 𝕊ᵢ)
  (finiteCond : FiniteConditions 𝓟 p)
  where

  open Parallelisation 𝓟 using (F; syncIter)
  open import RoutingLib.Data.Table.IndexedTypes 𝕊ᵢ
  open Membership 𝕊 using () renaming (_∈_ to _∈ₗ_)
  open Sublist 𝕊 using () renaming (_⊆_ to _⊆ₗ_)
  
  open FiniteConditions finiteCond

  x≼y≼z∧x≉y⇒x≉z : ∀ {x y z} → x ≼ y → y ≼ z → x ≉ y → x ≉ z
  x≼y≼z∧x≉y⇒x≉z x≼y y≼z x≉y x≈z = x≉y (≼-antisym x≼y (≼-trans y≼z (≼-reflexive (≈-sym x≈z))))

  module _ {x₀} (x₀∈D₀ : x₀ ∈ D₀) where
  
    -- Synchronous iteration

    σ : ℕ → S
    σ = syncIter x₀

    -- The initial set

    D₀-complete : ∀ K → σ K ∈ D₀
    D₀-complete zero    i = x₀∈D₀ i
    D₀-complete (suc K) i = D₀-closed (σ K) (D₀-complete K) i

    σ-decreasing : ∀ K → σ (suc K) ≼ σ K
    σ-decreasing K i = F-nonexpansive (D₀-complete K) i

    σ-mono : ∀ {k t} → k ≤ t → σ t ≼ σ k
    σ-mono {_} {zero}  z≤n = ≼-refl
    σ-mono {k} {suc t} k≤t with k ≟ℕ suc t
    ... | yes refl = ≼-refl
    ... | no  k≢st = begin
      σ (suc t) ≤⟨ F-nonexpansive (D₀-complete t) ⟩
      σ t       ≤⟨ σ-mono {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)) ⟩
      σ k       ∎
      where open POR ≼-poset

    σ-fixed : ∀ K → σ K ≈ σ (suc K) → ∀ t → σ K ≈ σ (K + t)
    σ-fixed K σ[K]≈σ[1+K] zero    = ≈-cong (σ) (sym (+-identityʳ K))
    σ-fixed K σ[K]≈σ[1+K] (suc t) = begin
      σ K           ≈⟨ σ[K]≈σ[1+K] ⟩
      σ (suc K)     ≈⟨ σ-fixed (suc K) (F-cong σ[K]≈σ[1+K]) t ⟩
      σ (suc K + t) ≡⟨ cong σ (sym (+-suc K t)) ⟩
      σ (K + suc t) ∎
      where open EqReasoning 𝕊

    -- List of all states
    D₀ˡ : List S
    D₀ˡ = proj₁ D₀-finite

    σ[K]∈D₀ˡ : ∀ K → σ K ∈ₗ D₀ˡ
    σ[K]∈D₀ˡ K = proj₂ D₀-finite (D₀-complete K)

    ≉σ[K]-cong : ∀ K {x y} → x ≈ y → σ K ≉ x → σ K ≉ y
    ≉σ[K]-cong _ x≈y x≉iterK iterK≈y = x≉iterK (≈-trans iterK≈y (≈-sym x≈y))

    -- List of states at each time step
    Dₖˡ : ℕ → List S
    Dₖˡ zero    = D₀ˡ
    Dₖˡ (suc K) = filter (∁? (σ K ≟_)) (Dₖˡ K)

    Dₖˡ-decreasing : ∀ K → Dₖˡ (suc K) ⊆ₗ  Dₖˡ K
    Dₖˡ-decreasing K x∈DsK = proj₁ (∈-filter⁻ 𝕊 (∁? (σ K ≟_)) (≉σ[K]-cong K) x∈DsK)

    σ[K]∈Dₜˡ : ∀ K → σ K ≉ σ (suc K) → ∀ {t} → t ≤ K → σ (suc K) ∈ₗ Dₖˡ t
    σ[K]∈Dₜˡ K _           {zero}  _   = σ[K]∈D₀ˡ (suc K)
    σ[K]∈Dₜˡ K σ[K]≉σ[1+K] {suc t} t≤K = ∈-filter⁺ 𝕊 (∁? (σ t ≟_))
      (≉σ[K]-cong t)
      (σ[K]∈Dₜˡ K σ[K]≉σ[1+K] (<⇒≤ t≤K))
      ((x≼y≼z∧x≉y⇒x≉z (σ-decreasing K) (σ-mono (<⇒≤ t≤K)) (σ[K]≉σ[1+K] ∘ ≈-sym)) ∘ ≈-sym)

    σ[K]∈Dₖˡ : ∀ K → σ K ≉ σ (suc K) → σ K ∈ₗ Dₖˡ K
    σ[K]∈Dₖˡ zero    _           = σ[K]∈D₀ˡ zero
    σ[K]∈Dₖˡ (suc K) σ[K]≉σ[1+K] = ∈-filter⁺ 𝕊 (∁? (σ K ≟_))
      (≉σ[K]-cong K)
      (σ[K]∈Dₜˡ K (σ[K]≉σ[1+K] ∘ F-cong) ≤-refl)
      (λ σ[K]≈σ[2+k] → σ[K]≉σ[1+K] (begin
        σ (1 + K) ≈⟨ ≈-sym σ[K]≈σ[2+k] ⟩
        σ K       ≈⟨ σ-fixed K σ[K]≈σ[2+k] 2 ⟩
        σ (K + 2) ≡⟨ cong σ (+-comm K 2) ⟩
        σ (2 + K) ∎))
      where open EqReasoning 𝕊

    |Dₖˡ|-decreasing : ∀ K → σ K ≉ σ (suc K) → length (Dₖˡ (suc K)) < length (Dₖˡ K)
    |Dₖˡ|-decreasing K σ[K]≉σ[1+K] = filter-notAll (∁? (σ K ≟_)) (Dₖˡ K) (Any.map contradiction (σ[K]∈Dₖˡ K σ[K]≉σ[1+K]))

    -- Prove that fixed point exists
    σ-fixedPoint : ∀ K → Acc _<_ (length (Dₖˡ K)) → ∃ λ T → ∀ t → σ T ≈ σ (T + t)
    σ-fixedPoint K (acc rec) with σ K ≟ σ (suc K)
    ... | yes σ[K]≈σ[1+K] = K , σ-fixed K σ[K]≈σ[1+K]
    ... | no  σ[K]≉σ[1+K] = σ-fixedPoint (suc K) (rec _ (|Dₖˡ|-decreasing K σ[K]≉σ[1+K]))

    σ-converges : ∃ λ T → ∀ t → σ T ≈ σ (T + t)
    σ-converges = σ-fixedPoint 0 (<-wellFounded (length D₀ˡ))

  syncCond : SynchronousConditions 𝓟 p
  syncCond = record
    { start           = start
    ; poset           = poset
    ; F-monotone      = F-monotone
    ; iter-decreasing = σ-decreasing
    ; iter-converge   = σ-converges 
    }
