open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⁅_⁆; _∪_; _∈_; _∉_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈p∪q⁺; x∈p∪q⁻; x∈⁅y⁆⇒x≡y; ∈⊤)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _^_; _*_; _<_; _≤_)
open import Data.Nat.Properties using (≤⇒pred≤; +-comm; +-suc; *-identityʳ; ≤-refl; <⇒≢; ≤+≢⇒<; ≤-irrelevance)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import Function using (_∘_)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset using (∣_∣; Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties
  using (∣p∣<n⇒Nonfull; ∣⁅i⁆∣≡1; ∣p∪⁅i⁆∣≡1+∣p∣; i∉⁅j⁆; Nonfull⁅i⁆′; x∉p∪q⁺; ∣p∣≡n⇒p≡⊤)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.NodeSets as NodeSets
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Proof as InductiveStep 
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.FixedSubtree as FixedSubtree
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.InductiveStep
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒


  module _ (X : RMatrix) (j : Fin n) where

    
    open FixedSubtree 𝓟𝓢𝓒 X j
    open NodeSets 𝓟𝓢𝓒 X j
    open InductiveStep 𝓟𝓢𝓒 X j
    
    mutual

      iᵗʰ : ∀ i → i < n → Fin n
      iᵗʰ zero    _     = j
      iᵗʰ (suc i) 1+i<n =
        iₘᵢₙ
          (i * n)
          (j∈F i (≤⇒pred≤ 1+i<n))
          (Fᵢ-nonfull i 1+i<n)
          (F-fixed i (≤⇒pred≤ 1+i<n))

      iᵗʰ∈Fixed : ∀ i (i<n : i < n) → iᵗʰ i i<n ∈ᵤ Fixed (suc (i * n))
      iᵗʰ∈Fixed zero    i<n   = j∈Fixed₁
      iᵗʰ∈Fixed (suc i) 1+i<n = Fixed-cong
        (iₘᵢₙ-fixed (i * n)
          (j∈F i (≤⇒pred≤ 1+i<n))
          (Fᵢ-nonfull i 1+i<n)
          (F-fixed i (≤⇒pred≤ 1+i<n)))
        (cong suc (+-comm (i * n) n))

      iᵗʰ≢kᵗʰ : ∀ i k (i<n : i < n) (k<n : k < n) → k < i → iᵗʰ i i<n ≢ iᵗʰ k k<n
      iᵗʰ≢kᵗʰ zero    _  i<n k<n ()
      iᵗʰ≢kᵗʰ (suc i) k  1+i<n k<n (s≤s k≤i) iᵗʰ≡kᵗʰ =
        iₘᵢₙ∉F
          (i * n)
          (j∈F i (≤⇒pred≤ 1+i<n))
          (Fᵢ-nonfull i 1+i<n)
          (F-fixed i (≤⇒pred≤ 1+i<n))
          (subst (_∈ F i (≤⇒pred≤ 1+i<n)) (sym iᵗʰ≡kᵗʰ) (
            iᵗʰ∈Fₖ k k<n i ((≤⇒pred≤ 1+i<n)) k≤i))

      F : ∀ i → i < n → Subset n
      F zero    0<n = ⁅ iᵗʰ zero 0<n ⁆
      F (suc i) 1+i<n = (F i (≤⇒pred≤ 1+i<n)) ∪ ⁅ iᵗʰ (suc i) 1+i<n ⁆

      j∈F : ∀ i → (i<n : i < n) → j ∈ F i i<n
      j∈F zero    _     = x∈⁅x⁆ j
      j∈F (suc i) 1+i<n = x∈p∪q⁺ (inj₁ (j∈F i (≤⇒pred≤ 1+i<n)))

      F-fixed : ∀ i {k} → (i<n : i < n) → k ∈ F i i<n → k ∈ᵤ Fixed (suc (i * n))
      F-fixed zero    {k} _     k∈F₁  = subst (_∈ᵤ Fixed 1) (sym (x∈⁅y⁆⇒x≡y j k∈F₁)) j∈Fixed₁
      F-fixed (suc i) {k} 1+i<n k∈F₁₊ᵢ with x∈p∪q⁻ (F i _) ⁅ iᵗʰ (suc i) _ ⁆ k∈F₁₊ᵢ
      ... | inj₂ k∈⁅1+iᵗʰ⁆ rewrite x∈⁅y⁆⇒x≡y _ k∈⁅1+iᵗʰ⁆ = iᵗʰ∈Fixed (suc i) 1+i<n
      ... | inj₁ k∈Fᵢ      = test3 --Fixedₜ⊆Fixedₛ₊ₜ (suc (i * n)) {!n-1!} (F-fixed i (≤⇒pred≤ 1+i<n) k∈Fᵢ)
        where

        test : k ∈ᵤ Fixed (suc (i * n))
        test = F-fixed i (≤⇒pred≤ 1+i<n) k∈Fᵢ

        test2 : k ∈ᵤ Fixed (n + suc (i * n))
        test2 = Fixedₜ⊆Fixedₛ₊ₜ (suc (i * n)) n test

        test3 : k ∈ᵤ Fixed (suc (n + i * n))
        test3 = Fixed-cong test2 (+-suc n (i * n))

      iᵗʰ∈Fₖ : ∀ i (i<n : i < n) k (k<n : k < n) → i ≤ k → iᵗʰ i i<n ∈ F k k<n
      iᵗʰ∈Fₖ zero   i<n zero     k<n z≤n = x∈⁅x⁆ j
      iᵗʰ∈Fₖ i      i<n (suc k)  k<n z≤n = j∈F (suc k) k<n
      iᵗʰ∈Fₖ (suc i) i<n zero    k<n ()
      iᵗʰ∈Fₖ (suc i) i<n (suc k) k<n (s≤s i≤k) with i ℕ.≟ k
      ... | no  i≢k = x∈p∪q⁺ (inj₁ (iᵗʰ∈Fₖ (suc i) i<n k (≤⇒pred≤ k<n) (≤+≢⇒< i≤k i≢k)))
      ... | yes refl with ≤-irrelevance k<n i<n
      ...   | refl = x∈p∪q⁺ (inj₂ (x∈⁅x⁆ (iᵗʰ (suc i) i<n)))
      
      iᵗʰ∉Fₖ : ∀ i (i<n : i < n) k (k<n : k < n) → k < i → iᵗʰ i i<n ∉ F k k<n
      iᵗʰ∉Fₖ zero    1<n    _   _   ()
      iᵗʰ∉Fₖ (suc i) 1+i<n zero k<n    k<i = i∉⁅j⁆ (iᵗʰ≢kᵗʰ (suc i) 0 1+i<n k<n k<i)
      iᵗʰ∉Fₖ (suc i) 1+i<n (suc k) 1+k<n k<i = x∉p∪q⁺
        (iᵗʰ∉Fₖ (suc i) 1+i<n k (≤⇒pred≤ 1+k<n) (≤⇒pred≤ k<i))
        (i∉⁅j⁆ (iᵗʰ≢kᵗʰ (suc i) (suc k) 1+i<n 1+k<n k<i))
      
      |Fᵢ|≡i : ∀ i → (i<n : i < n) → ∣ F i i<n ∣ ≡ suc i
      |Fᵢ|≡i zero    _     = ∣⁅i⁆∣≡1 j
      |Fᵢ|≡i (suc i) 1+i<n = trans
        (∣p∪⁅i⁆∣≡1+∣p∣ (iᵗʰ∉Fₖ (suc i) 1+i<n i (≤⇒pred≤ 1+i<n) ≤-refl))
        (cong suc (|Fᵢ|≡i i (≤⇒pred≤ 1+i<n)))
    
      Fᵢ-nonfull : ∀ i (1+i<n : suc i < n) → Nonfull (F i (≤⇒pred≤ 1+i<n))
      Fᵢ-nonfull i 1+i<n = ∣p∣<n⇒Nonfull (subst (_< n) (sym (|Fᵢ|≡i i (≤⇒pred≤ 1+i<n))) 1+i<n)
     

    
    
    Fₙ₋₁-complete : ∀ i → i ∈ F (n-1) ≤-refl 
    Fₙ₋₁-complete i = subst (i ∈_) (sym (∣p∣≡n⇒p≡⊤ (|Fᵢ|≡i (n-1) ≤-refl))) ∈⊤ 

    Fₙ₋₁-fixed′ : ∀ {i} → i ∈ F (n-1) ≤-refl → i ∈ᵤ Fixed (suc (n-1 * n))
    Fₙ₋₁-fixed′ i∈Fₙ₋₁ = F-fixed n-1 ≤-refl i∈Fₙ₋₁
    
    Fₙ₋₁-fixed : ∀ {i} → i ∈ F (n-1) ≤-refl → i ∈ᵤ Fixed (n ^ 2)
    Fₙ₋₁-fixed i∈Fₙ₋₁ = Fixed-cong (Fixedₜ⊆Fixedₛ₊ₜ (suc (n-1 * n)) n-1 (Fₙ₋₁-fixed′ i∈Fₙ₋₁)) v
      where
      v : n-1 + suc (n-1 * n) ≡ n ^ 2
      v rewrite *-identityʳ n-1 = +-suc n-1 _
    
  n²-convergence : ∀ X t → σ^ (n ^ 2 + t) X ≈ₘ σ^ (n ^ 2) X
  n²-convergence X t i j = proj₁ (Fₙ₋₁-fixed X j (Fₙ₋₁-complete X j i)) t

