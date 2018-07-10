open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?)
open import Data.List using (List; length; []; _∷_; filter)
open import Data.List.Any as Any using (Any; here; there)
import Data.List.Membership.Setoid as Membership
import Data.List.Relation.Sublist.Setoid as Sublist
open import Data.List.Membership.Setoid.Properties using (∈-filter⁻; ∈-filter⁺; ∈-resp-≈)
open import Data.List.Properties using (length-filter; filter-notAll)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≟_ to _≟ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties as ℕₚ using (+-suc; +-identityʳ; +-comm; ≤-step; m≤m+n; pred-mono; ≤+≢⇒<; <⇒≤)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_; map₂)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Poset; Reflexive; Antisymmetric; Transitive; _⇒_; Decidable)
open import Relation.Binary.PropositionalEquality using (subst; cong; _≡_; trans; sym; refl)
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary.Properties using (∁?)
open import Induction.Nat using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid)
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Convergence.Conditions
import RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois3 as Prop3

module RoutingLib.Asynchronous.Convergence.Proofs.UresinDubois4
  {a ℓ n p o}
  {𝕊ᵢ : Setoid (Fin n) a ℓ}
  (𝓟 : Parallelisation 𝕊ᵢ)
  (finiteCond : FiniteConditions 𝓟 p o)
  where

  open Parallelisation 𝓟

  open Membership setoid using () renaming (_∈_ to _∈ₗ_)
  open Sublist setoid using () renaming (_⊆_ to _⊆ₗ_)

  open FiniteConditions finiteCond

  -------------------------------------------------------
  -- This is currently a work in progress

  _≟_ : Decidable _≈_
  x ≟ y = all? (λ i → x i ≟ᵢ y i)

  ξ-fixed : F ξ ≈ ξ
  ξ-fixed = {!!}

  F-decr : ∀ {x} → x ∈ D₀ → F x ≤ x
  F-decr {x} x∈D₀ with x ≟ ξ
  ... | yes x≈ξ = ≤-reflexive (≈-trans (≈-trans (F-cong x≈ξ) ξ-fixed) (≈-sym x≈ξ))
  ... | no  x≉ξ = proj₁ (F-strictlyDecr x∈D₀ x≉ξ)

  {-
  x≤y≤z∧x≉y⇒x≉z : ∀ {x y z} → x ≤ y → y ≤ z → x ≉ y → x ≉ z
  x≤y≤z∧x≉y⇒x≉z x≤y y≤z x≉y x≈z = x≉y (≤-antisym x≤y (≤-trans y≤z (≤-reflexive (≈-sym x≈z))))

  ≤-poset : Poset _ _ _
  ≤-poset = record { isPartialOrder = isPartialOrder }


  D₀-complete : ∀ {x₀} → x₀ ∈ D₀ → ∀ K → syncIter x₀ K ∈ D₀
  D₀-complete x₀∈D₀ zero    = x₀∈D₀
  D₀-complete x₀∈D₀ (suc K) = D₀-closed (D₀-complete x₀∈D₀ K)

  iter-decreasing : ∀ {x₀} → x₀ ∈ D₀ → ∀ K → syncIter x₀ (suc K) ≤ syncIter x₀ K
  iter-decreasing x₀∈D₀ K i = F-nonexpansive (D₀-complete x₀∈D₀ K) ? i



  -- Synchronous iteration

  module _ {x₀} (x₀∈D₀ : x₀ ∈ D₀) where

    σ : ℕ → S
    σ = syncIter x₀

    -- The initial set

    σ-mono : ∀ {k t} → k ≤ℕ t → σ t ≤ σ k
    σ-mono {_} {zero}  z≤n = ≤-refl
    σ-mono {k} {suc t} k≤t with k ≟ℕ suc t
    ... | yes refl = ≤-refl
    ... | no  k≢st = begin
      σ (suc t) ≤⟨ F-nonexpansive (D₀-complete x₀∈D₀ t) ⟩
      σ t       ≤⟨ σ-mono {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)) ⟩
      σ k       ∎
      where open POR ≤-poset

    σ-fixed : ∀ K → σ (suc K) ≈ σ K  → ∀ t → σ (t + K) ≈ σ K
    σ-fixed K σ[1+K]≈σ[K] zero    rewrite +-identityʳ K = ≈-refl
    σ-fixed K σ[1+K]≈σ[K] (suc t) = begin
      σ (suc t + K) ≡⟨ sym (cong σ (+-suc t K)) ⟩
      σ (t + suc K) ≈⟨ σ-fixed (suc K) (F-cong σ[1+K]≈σ[K]) t ⟩
      σ (suc K)     ≈⟨ σ[1+K]≈σ[K] ⟩
      σ K           ∎
      where open EqReasoning setoid

    -- List of all states
    D₀ˡ : List S
    D₀ˡ = proj₁ D₀-finite

    σ[K]∈D₀ˡ : ∀ K → σ K ∈ₗ D₀ˡ
    σ[K]∈D₀ˡ K = proj₂ D₀-finite (D₀-complete x₀∈D₀ K)

    ≉σ[K]-cong : ∀ K {x y} → x ≈ y → σ K ≉ x → σ K ≉ y
    ≉σ[K]-cong _ x≈y x≉iterK iterK≈y = x≉iterK (≈-trans iterK≈y (≈-sym x≈y))

    -- List of states at each time step
    Dₖˡ : ℕ → List S
    Dₖˡ zero    = D₀ˡ
    Dₖˡ (suc K) = filter (∁? (σ K ≟_)) (Dₖˡ K) --filter (∁? (σ K ≟_)) (Dₖˡ K)

    Dₖˡ-decreasing : ∀ K → Dₖˡ (suc K) ⊆ₗ  Dₖˡ K
    Dₖˡ-decreasing K x∈DsK = proj₁ (∈-filter⁻ setoid (∁? (σ K ≟_)) (≉σ[K]-cong K) x∈DsK)

    σ[K]∈Dₜˡ : ∀ K → σ K ≉ σ (suc K) → ∀ {t} → t ≤ℕ K → σ (suc K) ∈ₗ Dₖˡ t
    σ[K]∈Dₜˡ K _           {zero}  _   = σ[K]∈D₀ˡ (suc K)
    σ[K]∈Dₜˡ K σ[K]≉σ[1+K] {suc t} t≤K = ∈-filter⁺ setoid (∁? (σ t ≟_))
      (≉σ[K]-cong t)
      (σ[K]∈Dₜˡ K σ[K]≉σ[1+K] (<⇒≤ t≤K))
      ((x≤y≤z∧x≉y⇒x≉z (iter-decreasing x₀∈D₀ K) (σ-mono (<⇒≤ t≤K)) (σ[K]≉σ[1+K] ∘ ≈-sym)) ∘ ≈-sym)

    σ[K]∈Dₖˡ : ∀ K → σ K ≉ σ (suc K) → σ K ∈ₗ Dₖˡ K
    σ[K]∈Dₖˡ zero    _           = σ[K]∈D₀ˡ zero
    σ[K]∈Dₖˡ (suc K) σ[K]≉σ[1+K] = ∈-filter⁺ setoid (∁? (σ K ≟_))
      (≉σ[K]-cong K)
      (σ[K]∈Dₜˡ K (σ[K]≉σ[1+K] ∘ F-cong) ℕₚ.≤-refl)
      (λ σ[K]≈σ[2+k] → σ[K]≉σ[1+K] (begin
        σ (1 + K) ≈⟨ ≈-sym σ[K]≈σ[2+k] ⟩
        σ K       ≈⟨ ≈-sym (σ-fixed K (≈-sym σ[K]≈σ[2+k]) 2) ⟩
        σ (2 + K) ∎))
      where open EqReasoning setoid

    |Dₖˡ|-decreasing : ∀ K → σ K ≉ σ (suc K) → length (Dₖˡ (suc K)) <ℕ length (Dₖˡ K)
    |Dₖˡ|-decreasing K σ[K]≉σ[1+K] = filter-notAll (∁? (σ K ≟_)) (Dₖˡ K) (Any.map contradiction (σ[K]∈Dₖˡ K σ[K]≉σ[1+K]))

    -- Prove that fixed point exists
    σ-fixedPoint : ∀ K → Acc _<ℕ_ (length (Dₖˡ K)) → ∃ λ T → ∀ t → σ (t + T) ≈ σ T
    σ-fixedPoint K (acc rec) with σ K ≟ σ (suc K)
    ... | yes σ[K]≈σ[1+K] = K , σ-fixed K (≈-sym σ[K]≈σ[1+K])
    ... | no  σ[K]≉σ[1+K] = σ-fixedPoint (suc K) (rec _ (|Dₖˡ|-decreasing K σ[K]≉σ[1+K]))

    σ-converges : ∃ λ T → ∀ t → σ (t + T) ≈ σ T
    σ-converges = σ-fixedPoint 0 (<-wellFounded (length D₀ˡ))

{-
  ξ : S
  ξ = syncIter v (proj₁ (σ-converges v∈D₀))

  ξ-fixed : F ξ ≈ ξ
  ξ-fixed = proj₂ (σ-converges v∈D₀) 1

  ξ-unique : ∀ {x} → F x ≈ x → x ≈ ξ
  ξ-unique Fx≈x = {!!}

  iter-converge : ∀ {x} → x ∈ D₀ → ∃ λ T → syncIter x T ≈ ξ
  iter-converge x∈D₀ = map₂ (λ eq → ξ-unique (eq 1)) (σ-converges x∈D₀)
-}

  syncCond : SynchronousConditions 𝓟 p o
  syncCond = record
    { D₀              = D₀
    ; D₀-cong         = D₀-cong
    ; D₀-closed       = D₀-closed
    ; _≤ᵢ_            = _≤ᵢ_
    ; ≤ᵢ-isPartialOrder = ≤ᵢ-isPartialOrder

    ; ξ               = ξ
    ; ξ-fixed         = ? --ξ-fixed
    ; F-monotone      = F-monotone
    ; F-cong          = F-cong
    ; iter-decreasing = iter-decreasing
    ; iter-converge   = ? --iter-converge
    }
-}
