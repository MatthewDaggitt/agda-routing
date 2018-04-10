open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (x∈⁅y⁆⇒x≡y)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (∁; U; Decidable)
  renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; invalid; valid; notThere; notHere; continue)
  renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Relation.Subpath
open import RoutingLib.Data.SimplePath.All
open import RoutingLib.Data.SimplePath.Properties
  using (∉-resp-≈ₚ)
open import RoutingLib.Data.Fin.Subset using ()
import RoutingLib.Data.List.Extrema as Extrema

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.Properties using (Iᵢᵢ≡1#; Iᵢⱼ≡0#; Iᵢⱼ≈0⊎1)
import RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime.NodeSets
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  (X : RoutingProblem.RMatrix 𝓡𝓟)
  (j : Fin (suc n-1))
  where
  
  open Prelude 𝓟𝓢𝓒

  ------------------------------------------------------------------------------
  -- Settled nodes (nodes that don't change their value after time t)

  Settled : 𝕋 → Node → Set _
  Settled t i = ∀ s → σ^ (t + s) X i j ≈ σ^ t X i j

  j∈Settled₁ : j ∈ᵤ Settled 1
  j∈Settled₁ s = σXᵢᵢ≈σYᵢᵢ (σ^ s X) X j

  Settledₜ⊆Settledₛ₊ₜ : ∀ t s → Settled t ⊆ᵤ Settled (t + s)
  Settledₜ⊆Settledₛ₊ₜ t s {i} i∈Sₜ u = begin
    σ^ ((t + s) + u) X i j  ≡⟨ cong (λ t → σ^ t X i j) (+-assoc t s u) ⟩
    σ^ (t + (s + u)) X i j  ≈⟨ i∈Sₜ (s + u) ⟩
    σ^ t             X i j  ≈⟨ ≈-sym (i∈Sₜ s)  ⟩
    σ^ (t + s) X i j  ∎
    where open EqReasoning S

  Settled-alignment : ∀ t {i} → i ∈ᵤ Settled t → ∀ {k l p e⇿p i∉p} →
                      path (σ^ t X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                      i ≡ l × σ^ t X i j ≈ A i k ▷ σ^ t X k j ×
                      path (σ^ t X k j) ≈ₚ valid p
  Settled-alignment t {i} i∈Sₜ p[σXᵢⱼ]≈uv∷p
    with ≈-reflexive (cong (λ t → σ^ t X i j) (+-comm 1 t))
  ... | σ¹⁺ᵗ≈σᵗ⁺¹ with p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ (σ^ t X) i j (≈ₚ-trans (path-cong (≈-trans σ¹⁺ᵗ≈σᵗ⁺¹ (i∈Sₜ 1))) p[σXᵢⱼ]≈uv∷p)
  ...   | i≡l , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p = i≡l , ≈-trans (≈-sym (i∈Sₜ 1)) (≈-trans (≈-sym σ¹⁺ᵗ≈σᵗ⁺¹) σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ) , p[σᵗXₖⱼ]≈p
  
  ------------------------------------------------------------------------------
  -- Fixed nodes (nodes for which all nodes they route through are fixed
  -- after time t)
    
  Fixed : 𝕋 → Node → Set _
  Fixed t i = i ∈ᵤ Settled t × Allₙ (Settled t) (path (σ^ t X i j))

  Fixed-cong : ∀ {s t k} → k ∈ᵤ Fixed s → s ≡ t → k ∈ᵤ Fixed t
  Fixed-cong k∈Fₛ refl = k∈Fₛ
  
  j∈Fixed₁ : j ∈ᵤ Fixed 1
  j∈Fixed₁ = j∈Settled₁ , Allₙ-resp-≈ₚ (valid []) (≈ₚ-sym (begin
    path (σ X j j) ≈⟨ path-cong (σXᵢᵢ≈Iᵢᵢ X j) ⟩
    path (I j j)   ≡⟨ cong path (P.Iᵢᵢ≡1# 𝓡𝓟 j) ⟩
    path 1#        ≈⟨ p₁≈[] ⟩
    valid []       ∎))
    where open EqReasoning (ℙₛ n)

  i∈Fixed₁ : ∀ {i} → i ∈ ⁅ j ⁆ → i ∈ᵤ Fixed 1
  i∈Fixed₁ i∈⁅j⁆ = subst (_∈ᵤ Fixed 1) (sym (x∈⁅y⁆⇒x≡y _ i∈⁅j⁆)) j∈Fixed₁
  
  Fixedₜ⊆Fixedₜ₊ₛ : ∀ t s → Fixed t ⊆ᵤ Fixed (t + s)
  Fixedₜ⊆Fixedₜ₊ₛ t s (i∈Sₜ , p∈Sₜ) =
    Settledₜ⊆Settledₛ₊ₜ t s i∈Sₜ ,
    mapₙ (Settledₜ⊆Settledₛ₊ₜ t s) (Allₙ-resp-≈ₚ p∈Sₜ (path-cong (≈-sym (i∈Sₜ s))) )

  Fixedₜ⊆Fixedₛ₊ₜ : ∀ t s → Fixed t ⊆ᵤ Fixed (s + t)
  Fixedₜ⊆Fixedₛ₊ₜ t s rewrite +-comm s t = Fixedₜ⊆Fixedₜ₊ₛ t s
  
  Fixed-path : ∀ t {i p} → path (σ^ t X i j) ≈ₚ p → i ∈ᵤ Fixed t → Allₙ (Fixed t) p
  Fixed-path t {i} {invalid}  _ _ = invalid
  Fixed-path t {i} {valid []} _ _ = valid []
  Fixed-path t {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p i∈Fₜ@(i∈Sₜ , ik∷p∈Sₜ)  
    with Settled-alignment t i∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
  ... | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p with Allₙ-resp-≈ₚ ik∷p∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
  ...   | (valid ([ _ , k∈Sₜ ]∷ p∈Sₜ)) with Allₙ-resp-≈ₚ (valid p∈Sₜ) (≈ₚ-sym p[σᵗXₖⱼ]≈p)
  ...     | k∈Fₜ with Fixed-path t p[σᵗXₖⱼ]≈p (k∈Sₜ , k∈Fₜ)
  ...       | valid p∈Fₜ = valid ([ i∈Fₜ , (k∈Sₜ , k∈Fₜ) ]∷ p∈Fₜ)

{-
  Fixed-path : ∀ t {i} → i ∈ᵤ Fixed t → Allₙ (Fixed t) (path (σ^ t X i j))
  Fixed-path t = inner ≈ₚ-refl
-}  

  Fixed-eq : ∀ t k s₁ s₂ → k ∈ᵤ Fixed t →
             σ^ (t + s₁) X k j ≈ σ^ (t + s₂) X k j
  Fixed-eq t k s₁ s₂ (k∈Sₜ , _) = begin
    σ^ (t + s₁) X k j ≈⟨ k∈Sₜ s₁ ⟩
    σ^ (t)      X k j ≈⟨ ≈-sym (k∈Sₜ s₂) ⟩
    σ^ (t + s₂) X k j ∎
    where open EqReasoning S
  
  ------------------------------------------------------------------------------
  -- Aligned edges

  Aligned : 𝕋 → Edge → Set _
  Aligned t (i , k) = σ^ t X i j ≈ A i k ▷ σ^ t X k j

  Aligned? : ∀ t → Decidable (Aligned t)
  Aligned? t (i , k) = σ^ t X i j ≟ A i k ▷ σ^ t X k j
  
  ------------------------------------------------------------------------------
  -- Real paths
  
  Real : 𝕋 → Node → Set ℓ
  Real t i = Allₑ (Aligned t) (path (σ^ t X i j))

  Real? : ∀ t → Decidable (Real t)
  Real? t i = allₑ? (Aligned? t) (path (σ^ t X i j))

  Real-cong : ∀ {s t k} → k ∈ᵤ Real s → s ≡ t → k ∈ᵤ Real t
  Real-cong k∈Rₛ refl = k∈Rₛ

  ¬Real-cong : ∀ {s t k} → k ∉ᵤ Real s → s ≡ t → k ∉ᵤ Real t
  ¬Real-cong k∉Rₛ refl = k∉Rₛ
  
  Real-alignment : ∀ t {i} → i ∈ᵤ Real (suc t) → ∀ {k l p e⇿p i∉p} →
                   path (σ^ (suc t) X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                   i ≡ l × σ^ (suc t) X i j ≈ A i k ▷ σ^ (suc t) X k j ×
                   path (σ^ (suc t) X k j) ≈ₚ valid p
  Real-alignment t {i} i∈R₁₊ₜ {k} p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
    with Allₑ-resp-≈ₚ i∈R₁₊ₜ p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
  ... | valid (σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ ∷ _)
      with p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ (σ^ t X) i j p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
  ...   | refl , _ , _
        with alignPathExtension (σ^ (suc t) X) i j k
          (≈ₚ-trans (path-cong (≈-sym σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ)) p[σ¹⁺ᵗXᵢⱼ]≈uv∷p)
  ...     | _ , _ , p[σ¹⁺ᵗXₖⱼ]≈p = refl , σ¹⁺ᵗXᵢⱼ≈Aᵢₖσ¹⁺ᵗXₖⱼ , p[σ¹⁺ᵗXₖⱼ]≈p


  Real-path : ∀ {t i p} → path (σ^ (suc t) X i j) ≈ₚ p →
          i ∈ᵤ Real (suc t) → Allₙ (Real (suc t)) p
  Real-path {_} {i} {invalid}  _ _ = invalid
  Real-path {_} {i} {valid []} _ _ = valid []
  Real-path {t} {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈vk∷p i∈R₁₊ₜ  
    with Allₑ-resp-≈ₚ i∈R₁₊ₜ p[σᵗXᵢⱼ]≈vk∷p 
  ... | valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pʳ) with Real-alignment t i∈R₁₊ₜ p[σᵗXᵢⱼ]≈vk∷p
  ...   | refl , _ , p[σ¹⁺ᵗXₖⱼ]≈p with Allₑ-resp-≈ₚ (valid pʳ) (≈ₚ-sym p[σ¹⁺ᵗXₖⱼ]≈p)
  ...     | k∈R₁₊ₜ with Real-path {t} p[σ¹⁺ᵗXₖⱼ]≈p k∈R₁₊ₜ
  ...       | valid allpʳ = valid ([ i∈R₁₊ₜ , k∈R₁₊ₜ ]∷ allpʳ)

  {-
  Real-path′ : ∀ {t i} → i ∈ᵤ Real (suc t) →
              Allₙ (Real (suc t)) (path (σ^ (suc t) X i j))
  Real-path′ {t} = Real-path ≈ₚ-refl
  -}
  
  Real-∅ : ∀ t i → path (σ^ t X i j) ≈ₚ invalid → i ∈ᵤ Real t
  Real-∅ _ _ p≡∅ = Allₑ-resp-≈ₚ invalid (≈ₚ-sym p≡∅)

  Real-[] : ∀ t i → path (σ^ t X i j) ≈ₚ valid [] → i ∈ᵤ Real t
  Real-[] _ _ p≡[] = Allₑ-resp-≈ₚ (valid []) (≈ₚ-sym p≡[])
  
  ¬Real-length : ∀ t i → i ∉ᵤ Real t → 1 ≤ size (σ^ t X i j)
  ¬Real-length t i i∉Rₜ with path (σ^ t X i j)
  ... | invalid               = contradiction invalid i∉Rₜ
  ... | valid []              = contradiction (valid []) i∉Rₜ
  ... | valid (e ∷ p ∣ _ ∣ _) = s≤s z≤n

  ¬Real-extension : ∀ t i → i ∉ᵤ Real (suc t) → ∃₂ λ k p → ∃₂ λ k∉p e↔p →
                    path (σ^ (suc t) X i j) ≈ₚ valid ((i , k) ∷ p ∣ k∉p ∣ e↔p) ×
                    σ^ (suc t) X i j ≈ A i k ▷ σ^ t X k j ×
                    path (σ^ t X k j) ≈ₚ valid p
  ¬Real-extension t i i∉R₁₊ₜ with path (σ^ (suc t) X i j) | inspect path (σ^ (suc t) X i j)
  ... | invalid  | _ = contradiction invalid i∉R₁₊ₜ
  ... | valid [] | _ = contradiction (valid []) i∉R₁₊ₜ
  ... | valid ((_ , k) ∷ p ∣ k∉p ∣ e↔p) | [ p[σ¹⁺ᵗ]≡ik∷p ]
    with p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ (σ^ t X) i j (≈ₚ-reflexive p[σ¹⁺ᵗ]≡ik∷p)
  ...   | refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p =
    k , p , k∉p , e↔p , ≈ₚ-refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p

  Fixed⊆Real : ∀ t {i p} → path (σ^ t X i j) ≈ₚ p → i ∈ᵤ Fixed t → i ∈ᵤ Real t
  Fixed⊆Real t {i} {invalid}  p[σᵗXᵢⱼ]≈∅  _ = Real-∅ t i p[σᵗXᵢⱼ]≈∅
  Fixed⊆Real t {i} {valid []} p[σᵗXᵢⱼ]≈[] _ = Real-[] t i p[σᵗXᵢⱼ]≈[]
  Fixed⊆Real t {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
    with Settled-alignment t i∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
  ... | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p with Fixed-path t p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
  ...   | valid ([ _ , k∈Fₜ ]∷ p∈Fₜ) with Fixed⊆Real t p[σᵗXₖⱼ]≈p k∈Fₜ
  ...     | k∈Rₜ with Allₑ-resp-≈ₚ k∈Rₜ p[σᵗXₖⱼ]≈p
  ...       | valid pˡ = Allₑ-resp-≈ₚ (valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pˡ)) (≈ₚ-sym p[σᵗXᵢⱼ]≈ik∷p)

  ¬Real⊆¬Fixed : ∀ {t i} → i ∉ᵤ Real t → i ∉ᵤ Fixed t
  ¬Real⊆¬Fixed {t} {i} i∉Rₜ i∈Fₜ = i∉Rₜ (Fixed⊆Real t ≈ₚ-refl i∈Fₜ)
