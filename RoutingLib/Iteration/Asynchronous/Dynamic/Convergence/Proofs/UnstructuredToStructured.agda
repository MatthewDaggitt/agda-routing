open import Data.Fin using (Fin; zero)
open import Data.Fin.Subset using (Subset; _∉_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
-- open import Relation.Unary

open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)
open import RoutingLib.Relation.Unary.Indexed hiding (_∉_)

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.UnstructuredToStructured
  {a ℓ n-1 p} (𝓘 : AsyncIterable a ℓ (suc n-1)) (aco : ACO 𝓘 p) where

open AsyncIterable 𝓘
open ACO aco

n : ℕ
n = suc n-1

module _ (e : Epoch) (q : Subset n) where

  B : ℕ → IPred Sᵢ p
  B = D e q

  F' : S → S
  F' = F e q

  σ : ℕ → S → S
  σ zero    x = x
  σ (suc i) x = F' (σ i x)
  

  -- Fixed points
  
  k* : ℕ
  k* = proj₁ (D-finish e q)

  x* : S
  x* = proj₁ (proj₂ (D-finish e q))

  k*≤k⇒x*∈Bᵏ : ∀ {k} → k* ≤ k → x* ∈ B k
  k*≤k⇒x*∈Bᵏ k*≤k = proj₁ ((proj₂ (proj₂ (D-finish e q))) k*≤k)
  
  k*≤k∧x∈Bᵏ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ B k → x ≈ x*
  k*≤k∧x∈Bᵏ⇒x≈x* k*≤k x∈Bₖ = proj₂ (proj₂ (proj₂ (D-finish e q)) k*≤k) x∈Bₖ



  -- New box definitions
  
  M : ℕ → IPred Sᵢ p
  M k = ⋃ ℕ (λ l → B (k + suc l) / B (k + l))
  
  N : ℕ → IPred Sᵢ (a ⊔ p ⊔ ℓ)
  N k = ⋃ ℕ (λ l i x → (∃ λ y → (y ∈ M k) × (σ l y i ≈ᵢ x)))

  C : ℕ → IPred Sᵢ (a ⊔ p ⊔ ℓ)
  C k = B k ∪ N k




{-
  M[k*]=∅ : ∀ {k} → k* ≤ k → Empty (M k)  
  M[k*]=∅ {k} k*≤k x x∈Mᵏ with x∈Mᵏ zero
  ... | (l , x∈B₁₊ₖ₊₁₊ₗ , x∉B₁₊ₖ₊ₗ) = x∉B₁₊ₖ₊ₗ (begin⟨ k*≤k⇒x*∈Bᵏ (≤-stepsʳ l k*≤k) zero ⟩
    ⇒ x* zero ∈ᵢ B (k + l) ∴⟨ Dᵢ-cong (≈ᵢ-sym (k*≤k∧x∈Bᵏ⇒x≈x* {!!} {!!} zero)) ⟩
    ⇒ x zero  ∈ᵢ B (k + l) ∎)

  N[k*]=∅ : ∀ {k} → k* ≤′ k → Empty (N k)
  N[k*]=∅ k*≤k x x∈Nᵏ = {!!}
-}

  N? : ∀ k → Decidable (N k)
  N? = {!!}





  M₁₊ₖ⊆Mₖ : ∀ k → M (suc k) ⊆[ Sᵢ ] M k
  M₁₊ₖ⊆Mₖ k {x} x∈M₁₊ₖ i with x∈M₁₊ₖ i
  ... | (l , x∈B₁₊ₖ₊₁₊ₗ , x∉B₁₊ₖ₊ₗ) =
    suc l ,
    subst (λ v → x i ∈ᵢ B v) (sym (+-suc k (suc l))) x∈B₁₊ₖ₊₁₊ₗ ,
    subst (λ v → x i ∉ᵢ B v) (sym (+-suc k l)) x∉B₁₊ₖ₊ₗ

  N₁₊ₖ⊆Nₖ : ∀ k → N (suc k) ⊆[ Sᵢ ] N k
  N₁₊ₖ⊆Nₖ k {x} x∈N₁₊ₖ i with x∈N₁₊ₖ i
  ... | (l , y , y∈M¹⁺ᵏ , σˡyᵢ≈xᵢ) = l , y , M₁₊ₖ⊆Mₖ k y∈M¹⁺ᵏ , σˡyᵢ≈xᵢ

  C₁₊ₖ⊆Cₖ : (∀ k → Decidable (B k)) → ∀ k → C (suc k) ⊆[ Sᵢ ] C k
  C₁₊ₖ⊆Cₖ B? k {x} x∈C₁₊ₖ i with N? (suc k) x
  ... | yes x∈N₁₊ₖ = inj₂ (N₁₊ₖ⊆Nₖ k x∈N₁₊ₖ i)
  ... | no  x∉N₁₊ₖ with x∈C₁₊ₖ i
  ...   | inj₂ x∈N₁₊ₖ = contradiction x∈N₁₊ₖ {!x∉N₁₊ₖ!}
  ...   | inj₁ x∈B₁₊ₖ = {!!}




  x∈Cₖ⇒Fx∈C₁₊ₖ : ∀ {k x} → WellFormed q x → x ∈ C k → F' x ∈ C (suc k)
  x∈Cₖ⇒Fx∈C₁₊ₖ {k} {x} q x∈Cₖ i = {!!}
  
