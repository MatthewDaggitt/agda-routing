open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⁅_⁆; ∣_∣; _∪_; _∈_; _∉_)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆; x∈p∪q⁺; x∈p∪q⁻; x∈⁅y⁆⇒x≡y; ∈⊤; ∣⁅x⁆∣≡1)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _^_; _*_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import Function using (_∘_)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties
  using (∣p∣<n⇒Nonfull; ∣p∪⁅i⁆∣≡1+∣p∣; i∉⁅j⁆; Nonfull⁅i⁆′; x∉p∪q⁺; ∣p∣≡n⇒p≡⊤)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing using (AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets as Step1_NodeSets
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree as Step2_ConvergedSubtree
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step4_InductiveStep as Step4_InductiveStep

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step5_Proof
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra (suc n-1))
  (isIncreasing : IsIncreasing algebra)
  (A : AdjacencyMatrix algebra (suc n-1))
  where

open Prelude isRoutingAlgebra isPathAlgebra A

module _ (X : RoutingMatrix) (j : Fin n) where

  open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j
  open Step2_ConvergedSubtree isRoutingAlgebra isPathAlgebra isIncreasing A X j
  open Step4_InductiveStep isRoutingAlgebra isPathAlgebra isIncreasing A X j

  mutual

    iᵗʰ : ∀ i → i < n → Fin n
    iᵗʰ zero    _     = j
    iᵗʰ (suc i) 1+i<n =
      iₘᵢₙ
        (i * n)
        (j∈C i (≤⇒pred≤ 1+i<n))
        (Cᵢ-nonfull i 1+i<n)
        (C-converged i (≤⇒pred≤ 1+i<n))

    iᵗʰ∈𝓒 : ∀ i (i<n : i < n) → iᵗʰ i i<n ∈ᵤ 𝓒 (suc (i * n))
    iᵗʰ∈𝓒 zero    i<n   = j∈𝓒₁
    iᵗʰ∈𝓒 (suc i) 1+i<n = 𝓒-cong
      (iₘᵢₙ∈𝓒ₜ₊ₙ (i * n)
        (j∈C i (≤⇒pred≤ 1+i<n))
        (Cᵢ-nonfull i 1+i<n)
        (C-converged i (≤⇒pred≤ 1+i<n)))
      (cong suc (+-comm (i * n) n))

    iᵗʰ≢kᵗʰ : ∀ i k (i<n : i < n) (k<n : k < n) → k < i → iᵗʰ i i<n ≢ iᵗʰ k k<n
    iᵗʰ≢kᵗʰ (suc i) k  1+i<n k<n (s≤s k≤i) iᵗʰ≡kᵗʰ =
      iₘᵢₙ∉C
        (i * n)
        (j∈C i (≤⇒pred≤ 1+i<n))
        (Cᵢ-nonfull i 1+i<n)
        (C-converged i (≤⇒pred≤ 1+i<n))
        (subst (_∈ C i (≤⇒pred≤ 1+i<n)) (sym iᵗʰ≡kᵗʰ) (
          iᵗʰ∈Cₖ k k<n i ((≤⇒pred≤ 1+i<n)) k≤i))

    C : ∀ i → i < n → Subset n
    C zero    0<n = ⁅ iᵗʰ zero 0<n ⁆
    C (suc i) 1+i<n = (C i (≤⇒pred≤ 1+i<n)) ∪ ⁅ iᵗʰ (suc i) 1+i<n ⁆

    j∈C : ∀ i → (i<n : i < n) → j ∈ C i i<n
    j∈C zero    _     = x∈⁅x⁆ j
    j∈C (suc i) 1+i<n = x∈p∪q⁺ (inj₁ (j∈C i (≤⇒pred≤ 1+i<n)))

    C-converged : ∀ i {k} → (i<n : i < n) → k ∈ C i i<n → k ∈ᵤ 𝓒 (suc (i * n))
    C-converged zero    {k} _     k∈C₁  = subst (_∈ᵤ 𝓒 1) (sym (x∈⁅y⁆⇒x≡y j k∈C₁)) j∈𝓒₁
    C-converged (suc i) {k} 1+i<n k∈C₁₊ᵢ with x∈p∪q⁻ (C i _) ⁅ iᵗʰ (suc i) _ ⁆ k∈C₁₊ᵢ
    ... | inj₂ k∈⁅1+iᵗʰ⁆ rewrite x∈⁅y⁆⇒x≡y _ k∈⁅1+iᵗʰ⁆ = iᵗʰ∈𝓒 (suc i) 1+i<n
    ... | inj₁ k∈Cᵢ      = test3
      where

      test : k ∈ᵤ 𝓒 (suc (i * n))
      test = C-converged i (≤⇒pred≤ 1+i<n) k∈Cᵢ

      test2 : k ∈ᵤ 𝓒 (n + suc (i * n))
      test2 = 𝓒ₜ⊆𝓒ₛ₊ₜ (suc (i * n)) n test

      test3 : k ∈ᵤ 𝓒 (suc (n + i * n))
      test3 = 𝓒-cong test2 (+-suc n (i * n))

    iᵗʰ∈Cₖ : ∀ i (i<n : i < n) k (k<n : k < n) → i ≤ k → iᵗʰ i i<n ∈ C k k<n
    iᵗʰ∈Cₖ zero   i<n zero     k<n z≤n = x∈⁅x⁆ j
    iᵗʰ∈Cₖ i      i<n (suc k)  k<n z≤n = j∈C (suc k) k<n
    iᵗʰ∈Cₖ (suc i) i<n (suc k) k<n (s≤s i≤k) with i ℕ.≟ k
    ... | no  i≢k = x∈p∪q⁺ (inj₁ (iᵗʰ∈Cₖ (suc i) i<n k (≤⇒pred≤ k<n) (≤∧≢⇒< i≤k i≢k)))
    ... | yes refl with ≤-irrelevant k<n i<n
    ...   | refl = x∈p∪q⁺ (inj₂ (x∈⁅x⁆ (iᵗʰ (suc i) i<n)))

    iᵗʰ∉Cₖ : ∀ i (i<n : i < n) k (k<n : k < n) → k < i → iᵗʰ i i<n ∉ C k k<n
    iᵗʰ∉Cₖ (suc i) 1+i<n zero    k<n   k<i = i∉⁅j⁆ (iᵗʰ≢kᵗʰ (suc i) 0 1+i<n k<n k<i)
    iᵗʰ∉Cₖ (suc i) 1+i<n (suc k) 1+k<n k<i = x∉p∪q⁺
      (iᵗʰ∉Cₖ (suc i) 1+i<n k (≤⇒pred≤ 1+k<n) (≤⇒pred≤ k<i))
      (i∉⁅j⁆ (iᵗʰ≢kᵗʰ (suc i) (suc k) 1+i<n 1+k<n k<i))

    |Cᵢ|≡i : ∀ i → (i<n : i < n) → ∣ C i i<n ∣ ≡ suc i
    |Cᵢ|≡i zero    _     = ∣⁅x⁆∣≡1 j
    |Cᵢ|≡i (suc i) 1+i<n = trans
      (∣p∪⁅i⁆∣≡1+∣p∣ (iᵗʰ∉Cₖ (suc i) 1+i<n i (≤⇒pred≤ 1+i<n) ≤-refl))
      (cong suc (|Cᵢ|≡i i (≤⇒pred≤ 1+i<n)))

    Cᵢ-nonfull : ∀ i (1+i<n : suc i < n) → Nonfull (C i (≤⇒pred≤ 1+i<n))
    Cᵢ-nonfull i 1+i<n = ∣p∣<n⇒Nonfull (subst (_< n) (sym (|Cᵢ|≡i i (≤⇒pred≤ 1+i<n))) 1+i<n)

  Cₙ₋₁-complete : ∀ i → i ∈ C (n-1) ≤-refl
  Cₙ₋₁-complete i = subst (i ∈_) (sym (∣p∣≡n⇒p≡⊤ (|Cᵢ|≡i (n-1) ≤-refl))) ∈⊤

  Cₙ₋₁-converged′ : ∀ {i} → i ∈ C (n-1) ≤-refl → i ∈ᵤ 𝓒 (suc (n-1 * n))
  Cₙ₋₁-converged′ i∈Cₙ₋₁ = C-converged n-1 ≤-refl i∈Cₙ₋₁

  Cₙ₋₁-converged : ∀ {i} → i ∈ C (n-1) ≤-refl → i ∈ᵤ 𝓒 (n ^ 2)
  Cₙ₋₁-converged i∈Cₙ₋₁ = 𝓒-cong (𝓒ₜ⊆𝓒ₛ₊ₜ (suc (n-1 * n)) n-1 (Cₙ₋₁-converged′ i∈Cₙ₋₁)) v
    where
    v : n-1 + suc (n-1 * n) ≡ n ^ 2
    v rewrite *-identityʳ n-1 = +-suc n-1 _

Tᶜᵒⁿᵛ : ℕ → ℕ
Tᶜᵒⁿᵛ n = n ^ 2

Tᶜᵒⁿᵛ-converged : ∀ X t → σ (Tᶜᵒⁿᵛ n + t) X ≈ₘ σ (Tᶜᵒⁿᵛ n) X
Tᶜᵒⁿᵛ-converged X t i j = proj₁ (Cₙ₋₁-converged X j (Cₙ₋₁-complete X j i)) t

