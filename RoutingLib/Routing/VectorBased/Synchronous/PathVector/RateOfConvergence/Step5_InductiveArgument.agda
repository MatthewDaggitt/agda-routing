open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⁅_⁆; ∣_∣; _∪_; _∈_; _∉_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈p∪q⁺; x∈p∪q⁻; x∈⁅y⁆⇒x≡y; ∈⊤; ∣⁅x⁆∣≡1; ∣p∣≡n⇒p≡⊤; x≢y⇒x∉⁅y⁆)
open import Data.Nat as ℕ using (ℕ; NonZero; zero; suc; z≤n; s≤s; _+_; _^_; _*_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Unit using ()
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import Function using (_∘_)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties
  using (∣p∣<n⇒Nonfull; ∣p∪⁅i⁆∣≡1+∣p∣; Nonfull⁅i⁆′; x∉p∪q⁺)

open import RoutingLib.Routing.Prelude using (AdjacencyMatrix; RoutingMatrix)
open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step4_InductiveStep as Step4_InductiveStep

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step5_InductiveArgument
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (iₘᵢₙ : ∀ t → ProvablyConvergedSubset t → Fin (suc n-1))
  (iₘᵢₙ∉C : ∀ t Cₜ → iₘᵢₙ t Cₜ ∉ ProvablyConvergedSubset.C Cₜ)
  (inc : ℕ)
  (iₘᵢₙ∈𝓒[t+inc] : ∀ t .{{_ : NonZero t}} Cₜ → iₘᵢₙ t Cₜ ∈ᵤ 𝓒 (t + inc))  where

open Prelude isRoutingAlgebra isPathAlgebra A
  
mutual
  converged : ∀ i → .(suc i < n) → ProvablyConvergedSubset (suc (i * inc))
  converged i 1+i<n = record
    { C         = C i (≤⇒pred≤ 1+i<n)
    ; j∈C       = j∈C i (≤⇒pred≤ 1+i<n)
    ; C-nonFull = Cᵢ-nonfull i 1+i<n
    ; C⊆𝓒ₜ      = C-converged i (≤⇒pred≤ 1+i<n)
    }

  iᵗʰ : ∀ i → .(i < n) → Fin n
  iᵗʰ zero    _     = j
  iᵗʰ (suc i) 1+i<n = iₘᵢₙ (suc (i * inc)) (converged i 1+i<n)

  iᵗʰ∈𝓒 : ∀ i .(i<n : i < n) → iᵗʰ i i<n ∈ᵤ 𝓒 (suc (i * inc))
  iᵗʰ∈𝓒 zero    i<n   = j∈𝓒₁
  iᵗʰ∈𝓒 (suc i) 1+i<n = 𝓒-cong
    (iₘᵢₙ∈𝓒[t+inc] (suc (i * inc)) (converged i 1+i<n))
    (cong suc (+-comm (i * inc) inc))

  iᵗʰ≢kᵗʰ : ∀ i k .(i<n : i < n) .(k<n : k < n) → k < i → iᵗʰ i i<n ≢ iᵗʰ k k<n
  iᵗʰ≢kᵗʰ (suc i) k  1+i<n k<n (s≤s k≤i) iᵗʰ≡kᵗʰ =
    iₘᵢₙ∉C (suc (i * inc)) (converged i 1+i<n)
      (subst (_∈ C i (≤⇒pred≤ 1+i<n)) (sym iᵗʰ≡kᵗʰ) (iᵗʰ∈Cₖ k k<n i ((≤⇒pred≤ 1+i<n)) k≤i))

  C : ∀ i → .(i < n) → Subset n
  C zero    0<n   = ⁅ iᵗʰ zero 0<n ⁆
  C (suc i) 1+i<n = C i (≤⇒pred≤ 1+i<n) ∪ ⁅ iᵗʰ (suc i) 1+i<n ⁆

  j∈C : ∀ i → .(i<n : i < n) → j ∈ C i i<n
  j∈C zero    _     = x∈⁅x⁆ j
  j∈C (suc i) 1+i<n = x∈p∪q⁺ (inj₁ (j∈C i (≤⇒pred≤ 1+i<n)))

  C-converged : ∀ i {k} → .(i<n : i < n) → k ∈ C i i<n → k ∈ᵤ 𝓒 (suc (i * inc))
  C-converged zero    {k} _     k∈C₁  = subst (_∈ᵤ 𝓒 1) (sym (x∈⁅y⁆⇒x≡y j k∈C₁)) j∈𝓒₁
  C-converged (suc i) {k} 1+i<n k∈C₁₊ᵢ
    with x∈p∪q⁻ (C i _) ⁅ iᵗʰ (suc i) _ ⁆ k∈C₁₊ᵢ | iᵗʰ∈𝓒 (suc i) 1+i<n
  ... | inj₂ k∈⁅1+iᵗʰ⁆ | i+1ᵗʰ∈𝓒 rewrite x∈⁅y⁆⇒x≡y _ k∈⁅1+iᵗʰ⁆ = i+1ᵗʰ∈𝓒
  ... | inj₁ k∈Cᵢ      | i+1ᵗʰ∈𝓒 = 𝓒-cong test2 (+-suc inc (i * inc))
    where
    test : k ∈ᵤ 𝓒 (suc (i * inc))
    test = C-converged i (≤⇒pred≤ 1+i<n) k∈Cᵢ

    test2 : k ∈ᵤ 𝓒 (inc + suc (i * inc))
    test2 = 𝓒ₜ⊆𝓒ₛ₊ₜ (suc (i * inc)) inc test

  iᵗʰ∈Cₖ : ∀ i .(i<n : i < n) k .(k<n : k < n) → i ≤ k → iᵗʰ i i<n ∈ C k k<n
  iᵗʰ∈Cₖ zero    i<n zero    k<n z≤n = x∈⁅x⁆ j
  iᵗʰ∈Cₖ i       i<n (suc k) k<n z≤n = j∈C (suc k) k<n
  iᵗʰ∈Cₖ (suc i) i<n (suc k) k<n (s≤s i≤k) with i ℕ.≟ k | iᵗʰ∈Cₖ (suc i) i<n k | x∈⁅x⁆ (iᵗʰ (suc i) i<n)
  ... | no  i≢k  | rec₁ | rec₂ = x∈p∪q⁺ (inj₁ (rec₁ (≤⇒pred≤ k<n) (≤∧≢⇒< i≤k i≢k)))
  ... | yes refl | rec₁ | rec₂ = x∈p∪q⁺ (inj₂ rec₂)

  iᵗʰ∉Cₖ : ∀ i .(i<n : i < n) k .(k<n : k < n) → k < i → iᵗʰ i i<n ∉ C k k<n
  iᵗʰ∉Cₖ (suc i) 1+i<n zero    k<n   k<i = x≢y⇒x∉⁅y⁆ (iᵗʰ≢kᵗʰ (suc i) 0 1+i<n k<n k<i)
  iᵗʰ∉Cₖ (suc i) 1+i<n (suc k) 1+k<n k<i = x∉p∪q⁺
    (iᵗʰ∉Cₖ (suc i) 1+i<n k (≤⇒pred≤ 1+k<n) (≤⇒pred≤ k<i))
    (x≢y⇒x∉⁅y⁆ (iᵗʰ≢kᵗʰ (suc i) (suc k) 1+i<n 1+k<n k<i))

  |Cᵢ|≡i : ∀ i → .(i<n : i < n) → ∣ C i i<n ∣ ≡ suc i
  |Cᵢ|≡i zero    _     = ∣⁅x⁆∣≡1 j
  |Cᵢ|≡i (suc i) 1+i<n = trans
    (∣p∪⁅i⁆∣≡1+∣p∣ (iᵗʰ∉Cₖ (suc i) 1+i<n i (≤⇒pred≤ 1+i<n) ≤-refl))
    (cong suc (|Cᵢ|≡i i (≤⇒pred≤ 1+i<n)))

  Cᵢ-nonfull : ∀ i .(1+i<n : suc i < n) → Nonfull (C i (≤⇒pred≤ 1+i<n))
  Cᵢ-nonfull i 1+i<n = ∣p∣<n⇒Nonfull (subst (_< n) (sym (|Cᵢ|≡i i (≤⇒pred≤ 1+i<n))) (recompute (suc i <? n) 1+i<n))

Cₙ₋₁-complete : ∀ i → i ∈ C n-1 ≤-refl
Cₙ₋₁-complete i = subst (i ∈_) (sym (∣p∣≡n⇒p≡⊤ (|Cᵢ|≡i n-1 ≤-refl))) ∈⊤

Cₙ₋₁-converged : ∀ i → i ∈ᵤ 𝓒 (suc (n-1 * inc))
Cₙ₋₁-converged i = C-converged n-1 ≤-refl (Cₙ₋₁-complete i)
