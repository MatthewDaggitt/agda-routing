-- imports
open import Computation
  using (Computation; ACO)
open import ScheduleDouble
  using (ScheduleDouble)
open import Data.Nat
  using (ℕ; _+_; _≤_; zero; suc; _<_; _≟_; s≤s; z≤n; _∸_; _≤?_; pred)
open import Data.Fin
  using (Fin)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; IsEquivalence; _⇒_)
open import Data.Product
  using (∃; _,_; proj₂; proj₁; _×_)
open import Induction.Nat
  using (<-well-founded)
open import Relation.Unary
  using (_∈_; Pred; _∩_; _∉_)
open import Induction.WellFounded
  using (Acc; acc)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; +-identityʳ; m≤m+n; <⇒≤;
        <⇒≤pred; ≤+≢⇒<; m+n∸m≡n; ≤-antisym; pred-mono; +-suc)
open import Relation.Binary.PropositionalEquality
  using (cong₂; subst; _≡_; cong) renaming (refl to ≡refl; sym to ≡sym; trans to ≡trans)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Fin.Subset
  using () renaming (_∈_ to _∈s_)
open import Function
  using (_∘_)
  
open Setoid
  using (Carrier; _≈_; isEquivalence)
open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_; begin_; _∎)

module ScheduleDouble.Iteration.Properties {a}{ℓ}{n}{S : Fin n → Setoid a ℓ}
  (c : Computation S)(s : ScheduleDouble n) where

  open import ScheduleDouble.Iteration s c
    using (async-iter)
  open ScheduleDouble.ScheduleDouble s
  open ScheduleDouble.Timing s
  open import ScheduleDouble.Properties s
    using (φ≤τ; τ-inc; nextActive-active; nextActiveφ<φs; prop1-iii)
  open Computation.Computation c
  open IsEquivalence

  φsK≤sk⇒τK≤βsK : ∀ k K i j → φ (suc K) ≤ suc k → τ K j ≤ β (suc k) i j
  φsK≤sk⇒τK≤βsK k K i j p = subst ((τ K j) ≤_)
          (cong (λ x → β x i j) (m+n∸m≡n p))
          (proj₂ (prop1-iii K i j (suc k ∸ (φ (suc K)))))


  module Theorem1 {x₀ : (i : Fin n) → Carrier (S i)}(aco : ACO c)(x₀∈D₀ : ∀ i → x₀ i ∈ (Computation.ACO.D aco) 0 i) where
    open Computation.ACO aco

    τK≤k⇒xₖ∈DK : ∀ k K i → τ K i ≤ k → (accₖ : Acc _<_ k) →
                           async-iter k x₀ accₖ i ∈ D K i
    τK≤k⇒xₖ∈DK zero K i τ≤k (acc rs) with M ≟ 0
    ... | no M≢0 = subst ((x₀ i) ∈_) (cong (λ k → D k i)
        (≤-antisym z≤n (subst (K ≤_) (≤-antisym τ≤k z≤n) (τ-inc K i))))
                  (x₀∈D₀ i)
    τK≤k⇒xₖ∈DK zero K i τ≤k (acc rs) | yes M≡0 with D-finish
    ...| (ξ , ξ∈D , x∈D⇒x≡ξ) =
               D-subst K i (ξ i) (x₀ i)
                 ((sym (isEquivalence (S i))) (x∈D⇒x≡ξ {x₀} 0 i
                 (subst (x₀ i ∈_) (cong (λ k → D k i) (≡sym (cong (_+ 0) M≡0)))
                   (x₀∈D₀ i))))
                  (subst (ξ i ∈_) (cong (λ k → D k i) (cong (_+ K) M≡0)) (ξ∈D K i))
    τK≤k⇒xₖ∈DK (suc k) K i τ≤sk (acc rs) with i ∈? α (suc k)
    τK≤k⇒xₖ∈DK (suc k) zero i τ≤sk (acc rs) | yes i∈α with M ≟ 0
    ... | no M≢0 with D-monotone 0 (≤+≢⇒< z≤n (M≢0 ∘ ≡sym))
    ... | ∈D1⇒∈D0 , _ = ∈D1⇒∈D0 i
                    (f (λ j → async-iter (β (suc k) i j) x₀
                      (rs (β (suc k) i j)
                      (s≤s (causality k i j))) j) i)
                    (c-monotone 0
                    (λ j → τK≤k⇒xₖ∈DK (β (suc k) i j) 0 j
                       z≤n
                       (rs (β (suc k) i j) (s≤s (causality k i j))))
                    i)
    τK≤k⇒xₖ∈DK (suc k) zero i τ≤sk (acc rs) | yes i∈α | yes M≡0 with D-finish
    ... | (ξ , ξ∈D , x∈D⇒x≡ξ) = D-subst 0 i (ξ i)
                          (f (λ j → async-iter (β (suc k) i j) x₀
                            (rs (β (suc k) i j) (s≤s (causality k i j))) j) i)
                          ((sym (isEquivalence (S i)))
                            (x∈D⇒x≡ξ
                              {f (λ j → async-iter (β (suc k) i j) x₀
                                (rs (β (suc k) i j) (s≤s (causality k i j))) j)}
                              1 i
                              (subst
                                ((f (λ j → async-iter (β (suc k) i j) x₀
                                  (rs (β (suc k) i j) (s≤s (causality k i j))) j)
                                  i) ∈_)
                        (cong (λ t → D t i) (≡sym (cong (_+ 1) M≡0)))
                        (c-monotone 0 (λ j → τK≤k⇒xₖ∈DK (β (suc k) i j) 0 j
                          z≤n
                          (rs (β (suc k) i j) (s≤s (causality k i j)))) i))))
                          (subst (ξ i ∈_) (cong (λ t → D t i) (cong (_+ 0) M≡0)) (ξ∈D 0 i))
    τK≤k⇒xₖ∈DK (suc k) (suc K) i τ≤sk (acc rs) | yes i∈α =
                    c-monotone K
                    (λ j → τK≤k⇒xₖ∈DK (β (suc k) i j) K j
                      (φsK≤sk⇒τK≤βsK k K i j (≤-trans (φ≤τ (suc K) i) τ≤sk))
                      (rs (β (suc k) i j) (s≤s (causality k i j))))
                    i
    τK≤k⇒xₖ∈DK (suc k) K i τ≤sk (acc rs) | no  i∉α with τ K i  ≟ (suc k)
    ... | yes τK≡sk = contradiction (subst (i ∈s_) (cong α τK≡sk) (nextActive-active (φ K) i)) i∉α
    ... | no  τK≢sk = τK≤k⇒xₖ∈DK k K i
                    (<⇒≤pred (≤+≢⇒< τ≤sk τK≢sk)) (rs k (≤-reflexive ≡refl))

    -- Theorem 1
    theorem1-proof :  (K₁ : ℕ) (i : Fin n) → (S i ≈ async-iter (φ (suc M) + K₁) x₀
                   (<-well-founded (φ (suc M) + K₁)) i) (proj₁ D-finish i)
    theorem1-proof K₁ i with D-finish
    ... | (ξ , ξ∈D , x∈D⇒x≡ξ) = x∈D⇒x≡ξ
                   {async-iter (φ (suc M) + K₁) x₀
                     (<-well-founded (φ (suc M) + K₁))}
                   0 i (τK≤k⇒xₖ∈DK (φ (suc M) + K₁) (M + 0) i
                   (begin
                      τ (M + 0) i ≤⟨ ≤-reflexive (cong₂ τ (+-identityʳ M) ≡refl) ⟩
                      τ M i ≤⟨ <⇒≤ (nextActiveφ<φs M i) ⟩
                      φ (suc M) ≤⟨ m≤m+n (φ (suc M)) K₁ ⟩
                      φ (suc M) + K₁ ∎
                    )
                   (<-well-founded (φ (suc M) + K₁)))

    theorem1 : ∃ λ K → ∀ K₁ i → (_≈_ (S i)) (async-iter (K + K₁) x₀
             (<-well-founded (K + K₁)) i) (proj₁ D-finish i)
    theorem1 = φ (suc M) , theorem1-proof
