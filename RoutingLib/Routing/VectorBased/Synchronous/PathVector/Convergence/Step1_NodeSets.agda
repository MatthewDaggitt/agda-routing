open import Data.Nat
open import Data.Fin using (Fin)

open import Data.Fin.Subset using (Subset; _∈_; _∉_)
open import Data.Unit using (⊤)
open import Data.Nat.Properties using (+-comm; +-assoc; ≤⇒≤″; +-suc)
open import Data.Product using (proj₁; proj₂; _,_; _×_; ∃; ∃₂; curry; uncurry)
open import Level using (_⊔_)
open import Function.Base using (flip; const)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (∁; U; Decidable)
  renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.Reasoning.Setoid as EqReasoning
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Unary using (Pred)
open import Relation.Nullary using (Dec)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Routing.Basics.Path.CertifiedI.AllVertices
open import RoutingLib.Routing.Basics.Path.CertifiedI.AllEdges
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (AdjacencyMatrix; RoutingMatrix)

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Step1_NodeSets
  {a b ℓ n-1}
  {algebra          : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra    : IsCertifiedPathAlgebra algebra (suc n-1))
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  where

open import RoutingLib.Routing.Algebra.Construct.Consistent isRoutingAlgebra isPathAlgebra A using (𝑪)
open import RoutingLib.Routing.VectorBased.Synchronous.PathVector.Convergence.Prelude isRoutingAlgebra isPathAlgebra A

open import RoutingLib.Routing.Basics.Assignment algebra n
open import RoutingLib.Routing.Basics.Assignment.Properties isRoutingAlgebra n

private
  variable
    p : Path n
    i : Node
    t : ℕ
    
------------------------------------------------------------------------------
-- Definitions

-- Extended by relation
_↝⟨_⟩_ : Node → 𝕋 → Node → Set ℓ
k ↝⟨ t ⟩ i = (k , σ t X k j) ↝[ A ] (i , σ t X i j)

-- Consistent nodes - nodes for whose current value is consistent with the
-- weight of its accompanying path.
𝓚 : 𝕋 → Node → Set _
𝓚 t i = 𝑪 (σ t X i j) × i ⇨[ path (σ t X i j) ]⇨ j × (i ≡ j → path (σ t X i j) ≈ₚ trivial)

-- Real nodes -- Nodes that are using paths that align with the
-- current routing choices of the other nodes in the network.
𝓡 : 𝕋 → Node → Set ℓ
𝓡 t i = Allₑ (uncurry (flip _↝⟨ t ⟩_)) (path (σ t X i j))

-- Fixed nodes -- nodes that don't change their value after time t
𝓕 : 𝕋 → Node → Set _
𝓕 t i = ∀ s → σ (t + s) X i j ≈ σ t X i j

-- Converged nodes -- nodes for which all nodes they route through are fixed
-- after time t
𝓒 : 𝕋 → Node → Set _
𝓒 t i = i ∈ᵤ 𝓕 t × Allᵥ (𝓕 t) (path (σ t X i j))

-- Globally optimal nodes -- nodes for which are and will always use the
-- best possible route for them through the graph
𝓖 : 𝕋 → Node → Set _
𝓖 t i = ∀ s p → i ⇨[ᵛ p ]⇨ j → σ (t + s) X i j ≤₊ weight A (valid p)

------------------------------------------------------------------------------
-- Properties of 𝓚

𝓚-∅ : ∀ t .{{_ : NonZero t}} i → path (σ t X i j) ≈ₚ invalid → i ∈ᵤ 𝓚 t
𝓚-∅ t i p≈∅ =
  p[σᵗXᵢⱼ]≈∅⇒σᵗXᵢⱼᶜ t X i j p≈∅ ,
  p[σᵗXᵢⱼ]≈∅⇒i⇨[p[σᵗXᵢⱼ]]⇨j X t i j p≈∅ ,
  λ {refl → r≈0⇒path[r]≈[] (σᵗXᵢᵢ≈0# t X i)}

𝓚-[] : ∀ t .{{_ : NonZero t}} i → path (σ t X i j) ≈ₚ trivial → i ∈ᵤ 𝓚 t
𝓚-[] t i p≈[] =
  p[σᵗXᵢⱼ]≈[]⇒σᵗXᵢⱼᶜ t X i j p≈[] ,
  p[σᵗXᵢⱼ]≈[]⇒i⇨[p[σᵗXᵢⱼ]]⇨j X t i j p≈[] ,
  const p≈[]

j∈𝓚ₜ⇒σᵗXⱼⱼ≈0# : ∀ t → j ∈ᵤ 𝓚 t → σ t X j j ≈ 0#
j∈𝓚ₜ⇒σᵗXⱼⱼ≈0# t (σᵗXⱼⱼᶜ , j⇨p⇨j , p[σᵗXⱼⱼ]≈[]) = begin
  σ t X j j                   ≈˘⟨ σᵗXⱼⱼᶜ ⟩
  weight A (path (σ t X j j)) ≈⟨ weight-cong (p[σᵗXⱼⱼ]≈[] refl) ⟩
  weight A trivial            ≡⟨⟩
  0#                          ∎
  where open EqReasoning S

------------------------------------------------------------------------------
-- Properties of Aligned

_↝⟨_⟩?_ : ∀ k t i → Dec (k ↝⟨ t ⟩ i)
k ↝⟨ t ⟩? i = (k , σ t X k j) ↝[ A ]? (i , σ t X i j)

------------------------------------------------------------------------------
-- Properties of 𝓡

𝓡? : ∀ t → Decidable (𝓡 t)
𝓡? t i = allₑ? (uncurry (flip _↝⟨ t ⟩?_)) (path (σ t X i j))

𝓡-cong : ∀ {s t} → i ∈ᵤ 𝓡 s → s ≡ t → i ∈ᵤ 𝓡 t
𝓡-cong k∈Rₛ refl = k∈Rₛ

¬𝓡-cong : ∀ {s t} → i ∉ᵤ 𝓡 s → s ≡ t → i ∉ᵤ 𝓡 t
¬𝓡-cong k∉Rₛ refl = k∉Rₛ

𝓡-∅ : ∀ t i → path (σ t X i j) ≈ₚ invalid → i ∈ᵤ 𝓡 t
𝓡-∅ _ _ p≡∅ = Allₑ-resp-≈ₚ invalid (≈ₚ-sym p≡∅)

𝓡-[] : ∀ t i → path (σ t X i j) ≈ₚ trivial → i ∈ᵤ 𝓡 t
𝓡-[] _ _ p≡[] = Allₑ-resp-≈ₚ trivial (≈ₚ-sym p≡[])


𝓡-alignment : ∀ t .{{_ : NonZero t}} → ∀ {i} → i ∈ᵤ 𝓡 t → ∀ {k l p e⇿p i∉p} → 
                 path (σ t X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                 i ≡ l × k ↝⟨ t ⟩ i × path (σ t X k j) ≈ₚ valid p
𝓡-alignment t@(suc t-1) {i} i∈R₁₊ₜ {k} p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
  with Allₑ-resp-≈ₚ i∈R₁₊ₜ p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
... | valid (i↝ₜk ∷ _)
    with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t-1 X) i j p[σ¹⁺ᵗXᵢⱼ]≈uv∷p
...   | refl , _ , _
      with ▷-alignment (A i k) (σ t X k j) (≈ₚ-trans (path-cong (proj₁ i↝ₜk)) p[σ¹⁺ᵗXᵢⱼ]≈uv∷p)
...     | _ , _ , p[σ¹⁺ᵗXₖⱼ]≈p = refl , i↝ₜk , p[σ¹⁺ᵗXₖⱼ]≈p


𝓡-path : ∀ t → .{{_ : NonZero t}} → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓡 t → Allᵥ (𝓡 t) p
𝓡-path {i} {invalid} t _ _ = invalid
𝓡-path {i} {trivial} t _ _ = trivial
𝓡-path {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} t p[σᵗXᵢⱼ]≈vk∷p i∈Rₜ
  with 𝓡-path {k} {valid p} t | Allₑ-resp-≈ₚ i∈Rₜ p[σᵗXᵢⱼ]≈vk∷p
... | rec | valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pʳ) with 𝓡-alignment t i∈Rₜ p[σᵗXᵢⱼ]≈vk∷p
...   | refl , _ , p[σᵗXₖⱼ]≈p with Allₑ-resp-≈ₚ (valid pʳ) (≈ₚ-sym p[σᵗXₖⱼ]≈p)
...     | k∈Rₜ with rec p[σᵗXₖⱼ]≈p k∈Rₜ
...       | valid allpʳ = valid ([ i∈Rₜ , k∈Rₜ ]∷ allpʳ)

∉𝓡⇒lengthOfPath>0 : ∀ t i → i ∉ᵤ 𝓡 t → 1 ≤ size (σ t X i j)
∉𝓡⇒lengthOfPath>0 t i i∉Rₜ with path (σ t X i j)
... | invalid               = contradiction invalid i∉Rₜ
... | trivial               = contradiction trivial i∉Rₜ
... | valid (e ∷ p ∣ _ ∣ _) = s≤s z≤n

¬𝓡-retraction : ∀ t i → i ∉ᵤ 𝓡 (suc t) → ∃₂ λ k p → ∃₂ λ k∉p e↔p →
                path (σ (suc t) X i j) ≈ₚ valid ((i , k) ∷ p ∣ k∉p ∣ e↔p) ×
                σ (suc t) X i j ≈ A i k ▷ σ t X k j ×
                path (σ t X k j) ≈ₚ valid p
¬𝓡-retraction t i i∉R₁₊ₜ with path (σ (suc t) X i j) in p[σ¹⁺ᵗ]≡ik∷p
... | invalid  = contradiction invalid i∉R₁₊ₜ
... | valid [] = contradiction trivial i∉R₁₊ₜ
... | valid ((_ , k) ∷ p ∣ k∉p ∣ e↔p)
  with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t X) i j (≈ₚ-reflexive p[σ¹⁺ᵗ]≡ik∷p)
...   | refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p =
  k , p , k∉p , e↔p , ≈ₚ-refl , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p

𝓡ₜ⊆𝓚ₜ : ∀ t .{{_ : NonZero t}} → 𝓡 t ⊆ᵤ 𝓚 t
𝓡ₜ⊆𝓚ₜ t = rec t ≈ₚ-refl
  where
  rec : ∀ t .{{_ : NonZero t}} → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓡 t → i ∈ᵤ 𝓚 t
  rec {i} {invalid} t p[σᵗXᵢⱼ]≈∅  _ = 𝓚-∅ t i p[σᵗXᵢⱼ]≈∅
  rec {i} {trivial} t p[σᵗXᵢⱼ]≈[] _ = 𝓚-[] t i p[σᵗXᵢⱼ]≈[]
  rec {i} {valid p@((_ , k) ∷ q ∣ _ ∣ _)} t p[σᵗXᵢⱼ]≈ik∷q i∈𝓡ₜ
    with 𝓡-alignment t i∈𝓡ₜ p[σᵗXᵢⱼ]≈ik∷q | rec {k} {valid q} t
  ... | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈q | hyp with 𝓡-path t p[σᵗXᵢⱼ]≈ik∷q i∈𝓡ₜ
  ...   | valid ([ _ , k∈𝓡ₜ ]∷ q∈𝓡ₜ) with hyp p[σᵗXₖⱼ]≈q k∈𝓡ₜ
  ...     | (σᵗXₖⱼᶜ , k⇨p[σᵗXₖⱼ]⇨j , i≢j⇒σᵗXₖⱼ≈[]) =
    (begin
      weight A (path (σ t X i j))         ≈⟨ weight-cong p[σᵗXᵢⱼ]≈ik∷q ⟩
      weight A (valid p)                  ≡⟨⟩
      A i k ▷ weight A (valid q)          ≈˘⟨ ▷-cong (A i k) (weight-cong p[σᵗXₖⱼ]≈q) ⟩
      A i k ▷ weight A (path (σ t X k j)) ≈⟨ ▷-cong (A i k) σᵗXₖⱼᶜ ⟩
      A i k ▷ σ t X k j                   ≈⟨ proj₁ σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ⟩
      σ t X i j                           ∎) ,
    ⇨[]⇨-resp-≈ₚ (≈ₚ-sym p[σᵗXᵢⱼ]≈ik∷q)
      (valid (⇨∷⇨ (drop-valid
        (⇨[]⇨-resp-≈ₚ p[σᵗXₖⱼ]≈q k⇨p[σᵗXₖⱼ]⇨j)))) ,
    λ {refl → r≈0⇒path[r]≈[] (σᵗXᵢᵢ≈0# t X i)}
    where open EqReasoning S

------------------------------------------------------------------------------
-- Properties of 𝓕

𝓕ₜ⊆𝓕ₜ₊ₛ : ∀ t s → 𝓕 t ⊆ᵤ 𝓕 (t + s)
𝓕ₜ⊆𝓕ₜ₊ₛ t s {i} i∈Fₜ r = begin
  σ ((t + s) + r) X i j  ≡⟨ cong (λ t → σ t X i j) (+-assoc t s r) ⟩
  σ (t + (s + r)) X i j  ≈⟨ i∈Fₜ (s + r) ⟩
  σ t             X i j  ≈⟨ ≈-sym (i∈Fₜ s)  ⟩
  σ (t + s) X i j        ∎
  where open EqReasoning S

j∈𝓕₁ : j ∈ᵤ 𝓕 1 
j∈𝓕₁ s = FXᵢᵢ≈FYᵢᵢ (σ s X) X refl

j∈𝓕ₜ : ∀ t .{{_ : NonZero t}} → j ∈ᵤ 𝓕 t
j∈𝓕ₜ (suc t) = 𝓕ₜ⊆𝓕ₜ₊ₛ 1 t j∈𝓕₁

j∈𝓚⇒j∈𝓕 : ∀ t → j ∈ᵤ 𝓚 t → j ∈ᵤ 𝓕 t
j∈𝓚⇒j∈𝓕 zero    j∈𝓚ₜ zero    = ≈-refl
j∈𝓚⇒j∈𝓕 zero    j∈𝓚ₜ (suc s) = ≈-trans (σᵗXᵢᵢ≈0# (suc s) X j) (≈-sym (j∈𝓚ₜ⇒σᵗXⱼⱼ≈0# 0 j∈𝓚ₜ))
j∈𝓚⇒j∈𝓕 (suc t) j∈𝓚ₜ s       = j∈𝓕ₜ (suc t) s

𝓕-alignment : ∀ t → i ∈ᵤ 𝓕 t → ∀ {k l p e⇿p i∉p} →
               path (σ t X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
               i ≡ l × k ↝⟨ t ⟩ i × path (σ t X k j) ≈ₚ valid p
𝓕-alignment {i} t i∈Sₜ {k} p[σXᵢⱼ]≈uv∷p
  with ≈-reflexive (cong (λ t → σ t X i j) (+-comm 1 t))
... | σ¹⁺ᵗ≈σᵗ⁺¹ with p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ (σ t X) i j (≈ₚ-trans (path-cong (≈-trans σ¹⁺ᵗ≈σᵗ⁺¹ (i∈Sₜ 1))) p[σXᵢⱼ]≈uv∷p)
...   | i≡l , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p = i≡l , (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , σᵗXᵢⱼ≉∞) , p[σᵗXₖⱼ]≈p
  where
  σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ = ≈-trans (≈-trans (≈-sym σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ) σ¹⁺ᵗ≈σᵗ⁺¹) (i∈Sₜ 1)

  σᵗXᵢⱼ≉∞ : σ t X k j ≉ ∞#
  σᵗXᵢⱼ≉∞ σᵗXₖⱼ≈∞ = contradiction (≈ₚ-trans (≈ₚ-sym (r≈∞⇒path[r]≈∅ σᵗXₖⱼ≈∞)) p[σᵗXₖⱼ]≈p) λ()
  
------------------------------------------------------------------------------
-- Properties of 𝓒

𝓒-cong : ∀ {s t k} → k ∈ᵤ 𝓒 s → s ≡ t → k ∈ᵤ 𝓒 t
𝓒-cong k∈Fₛ refl = k∈Fₛ

𝓒ₜ⊆𝓒ₜ₊ₛ : ∀ t s → 𝓒 t ⊆ᵤ 𝓒 (t + s)
𝓒ₜ⊆𝓒ₜ₊ₛ t s (i∈Sₜ , p∈Sₜ) =
  𝓕ₜ⊆𝓕ₜ₊ₛ t s i∈Sₜ ,
  mapᵥ (𝓕ₜ⊆𝓕ₜ₊ₛ t s) (Allᵥ-resp-≈ₚ p∈Sₜ (path-cong (≈-sym (i∈Sₜ s))) )

𝓒ₜ⊆𝓒ₛ₊ₜ : ∀ t s → 𝓒 t ⊆ᵤ 𝓒 (s + t)
𝓒ₜ⊆𝓒ₛ₊ₜ t s rewrite +-comm s t = 𝓒ₜ⊆𝓒ₜ₊ₛ t s

𝓒-mono-≤ : ∀ {t s} → t ≤ s → 𝓒 t ⊆ᵤ 𝓒 s
𝓒-mono-≤ {t} t≤s with ≤⇒≤″ t≤s
... | less-than-or-equal {k} refl = 𝓒ₜ⊆𝓒ₜ₊ₛ t k

j∈𝓒₁ : j ∈ᵤ 𝓒 1
j∈𝓒₁ = j∈𝓕₁ , Allᵥ-resp-≈ₚ trivial (≈ₚ-sym (begin
  path (F X j j) ≈⟨ path-cong (FXᵢᵢ≈Iᵢᵢ X j) ⟩
  path (I j j)   ≡⟨ cong path (Iᵢᵢ≡0# j) ⟩
  path 0#        ≈⟨ p[0]≈[] ⟩
  trivial        ∎))
  where open EqReasoning (ℙₛ n)

j∈𝓒ₜ : ∀ t .{{_ : NonZero t}} → j ∈ᵤ 𝓒 t
j∈𝓒ₜ (suc t) = 𝓒ₜ⊆𝓒ₜ₊ₛ 1 t j∈𝓒₁

j∈𝓚⇒j∈𝓒 : ∀ t → j ∈ᵤ 𝓚 t → j ∈ᵤ 𝓒 t
j∈𝓚⇒j∈𝓒 t j∈𝓚ₜ@(_ , _ , i≡j⇒p≈[]) = j∈𝓚⇒j∈𝓕 t j∈𝓚ₜ , Allᵥ-resp-≈ₚ (valid []) (≈ₚ-sym (i≡j⇒p≈[] refl))

𝓒-path : ∀ t {i p} → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓒 t → Allᵥ (𝓒 t) p
𝓒-path t {i} {invalid} _ _ = invalid
𝓒-path t {i} {trivial} _ _ = trivial
𝓒-path t {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p i∈𝓒ₜ@(i∈𝓕ₜ , ik∷p∈𝓕ₜ)
  with 𝓒-path t {k} {valid p} | 𝓕-alignment t i∈𝓕ₜ p[σᵗXᵢⱼ]≈ik∷p
... | rec | refl , _ , p[σᵗXₖⱼ]≈p with Allᵥ-resp-≈ₚ ik∷p∈𝓕ₜ p[σᵗXᵢⱼ]≈ik∷p
...   | (valid ([ _ , k∈𝓕ₜ ]∷ p∈𝓕ₜ)) with Allᵥ-resp-≈ₚ (valid p∈𝓕ₜ) (≈ₚ-sym p[σᵗXₖⱼ]≈p)
...     | k∈𝓒ₜ with rec p[σᵗXₖⱼ]≈p (k∈𝓕ₜ , k∈𝓒ₜ)
...       | valid p∈𝓒ₜ = valid ([ i∈𝓒ₜ , (k∈𝓕ₜ , k∈𝓒ₜ) ]∷ p∈𝓒ₜ)

𝓒-eq : ∀ t k s₁ s₂ → k ∈ᵤ 𝓒 t → σ (t + s₁) X k j ≈ σ (t + s₂) X k j
𝓒-eq t k s₁ s₂ (k∈Sₜ , _) = begin
  σ (t + s₁) X k j ≈⟨  k∈Sₜ s₁ ⟩
  σ (t)      X k j ≈˘⟨ k∈Sₜ s₂ ⟩
  σ (t + s₂) X k j ∎
  where open EqReasoning S

𝓒ₜ⊆𝓕ₜ : ∀ t → 𝓒 t ⊆ᵤ 𝓕 t
𝓒ₜ⊆𝓕ₜ t = proj₁

𝓒ₜ⊆𝓡ₜ : ∀ t → path (σ t X i j) ≈ₚ p → i ∈ᵤ 𝓒 t → i ∈ᵤ 𝓡 t
𝓒ₜ⊆𝓡ₜ {i} {invalid} t p[σᵗXᵢⱼ]≈∅  _ = 𝓡-∅ t i p[σᵗXᵢⱼ]≈∅
𝓒ₜ⊆𝓡ₜ {i} {trivial} t p[σᵗXᵢⱼ]≈[] _ = 𝓡-[] t i p[σᵗXᵢⱼ]≈[]
𝓒ₜ⊆𝓡ₜ {i} {valid ((_ , k) ∷ p ∣ _ ∣ _)} t p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
  with 𝓒ₜ⊆𝓡ₜ {k} {valid p} t | 𝓕-alignment t i∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
... | rec | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p with 𝓒-path t p[σᵗXᵢⱼ]≈ik∷p (i∈Sₜ , ik∷p∈Fₜ)
...   | valid ([ _ , k∈Fₜ ]∷ p∈Fₜ) with Allₑ-resp-≈ₚ (rec p[σᵗXₖⱼ]≈p k∈Fₜ) p[σᵗXₖⱼ]≈p
...     | valid pˡ = Allₑ-resp-≈ₚ (valid (σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ ∷ pˡ)) (≈ₚ-sym p[σᵗXᵢⱼ]≈ik∷p)

¬𝓡⊆¬𝓒 : i ∉ᵤ 𝓡 t → i ∉ᵤ 𝓒 t
¬𝓡⊆¬𝓒 {t = t} i∉Rₜ i∈Fₜ = i∉Rₜ (𝓒ₜ⊆𝓡ₜ t ≈ₚ-refl i∈Fₜ)

------------------------------------------------------------------------------
-- Properties of 𝓖

𝓖ₜ⊆𝓖ₜ₊ₛ : ∀ t s → 𝓖 t ⊆ᵤ 𝓖 (t + s)
𝓖ₜ⊆𝓖ₜ₊ₛ t s {i} i∈𝓖ₜ r p i⇨p⇨j =
  subst (_≤₊ _) (cong (λ v → σ v X i j) (sym (+-assoc t s r))) (i∈𝓖ₜ (s + r) p i⇨p⇨j)

j∈𝓖₁ : j ∈ᵤ 𝓖 1
j∈𝓖₁ s p _ = ≤₊-respˡ-≈ (≈-sym (σᵗXᵢᵢ≈0# 1 (σ s X) j)) (≤₊-minimum _)

j∈𝓖ₜ : ∀ t .{{_ : NonZero t}} → j ∈ᵤ 𝓖 t
j∈𝓖ₜ (suc t) = 𝓖ₜ⊆𝓖ₜ₊ₛ 1 t j∈𝓖₁

j∈𝓚⇒j∈𝓖 : ∀ t → j ∈ᵤ 𝓚 t → j ∈ᵤ 𝓖 t
j∈𝓚⇒j∈𝓖 zero j∈𝓚ₜ zero p _ = begin
  σ 0 X j j           ≈⟨ j∈𝓚ₜ⇒σᵗXⱼⱼ≈0# 0 j∈𝓚ₜ ⟩
  0#                  ≤⟨ ≤₊-minimum (weight A (valid p)) ⟩
  weight A (valid p)  ∎
  where open POR ≤₊-poset
j∈𝓚⇒j∈𝓖 t     j∈𝓚ₜ (suc s) p _ = begin
  σ (t + suc s) X j j ≡⟨ cong (λ v → σ v X j j) (+-suc t s) ⟩
  σ (suc t + s) X j j ≈⟨ σᵗXᵢᵢ≈0# (suc t + s) X j ⟩
  0#                  ≤⟨ ≤₊-minimum (weight A (valid p)) ⟩
  weight A (valid p)  ∎
  where open POR ≤₊-poset
j∈𝓚⇒j∈𝓖 (suc t) j∈𝓚ₜ s       p _ = begin
  σ (suc t + s) X j j ≈⟨ σᵗXᵢᵢ≈0# (suc t + s) X j ⟩
  0#                  ≤⟨ ≤₊-minimum (weight A (valid p)) ⟩
  weight A (valid p)  ∎
  where open POR ≤₊-poset

𝓖-mono-≤ : ∀ {t s} → t ≤ s → 𝓖 t ⊆ᵤ 𝓖 s
𝓖-mono-≤ {t} t≤s with ≤⇒≤″ t≤s
... | less-than-or-equal {k} refl = 𝓖ₜ⊆𝓖ₜ₊ₛ t k
