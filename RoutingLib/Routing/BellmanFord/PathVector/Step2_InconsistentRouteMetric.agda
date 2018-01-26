open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; map)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _⊔_)
open import Data.Nat.Properties
  using (≤-reflexive; ≤-total; ⊔-comm; ⊔-identityʳ; m≤m⊔n)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Data.Nat.Properties
  using (⊔-monoˡ-≤; ⊔-triangulate; m≤o⇒m≤n⊔o; m<n⇒n≢0; n≤m×o≤m⇒n⊔o≤m; m<n⊎m<o⇒m<n⊔o; n≤m⇒m⊔n≡m;
        module ≤-Reasoning; ≤⇒≯)
import RoutingLib.Function.Distance as Distance

open import RoutingLib.Data.Sum using (flip)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step1_InconsistentHeightFunction as Step1

module RoutingLib.Routing.BellmanFord.PathVector.Step2_InconsistentRouteMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open Step1 𝓟𝓢𝓒 using
    ( hⁱ ; Hⁱ ; hⁱ-cong ; 1≤hⁱ; hⁱ≤Hⁱ ; hⁱ-decr ; h[sᶜ]<h[rⁱ] )
 
  open Distance S using (Ultrametric; IsUltrametric; MaxTriangleIneq; Bounded)

  private

    h-force-𝑰 : ∀ {x y} → 𝑰 x ⊎ 𝑰 y → hⁱ x ≤ hⁱ y → 𝑰 y
    h-force-𝑰 (inj₂ yⁱ) hx≤hy yᶜ = yⁱ yᶜ
    h-force-𝑰 (inj₁ xⁱ) hx≤hy yᶜ = contradiction (h[sᶜ]<h[rⁱ] yᶜ xⁱ) (≤⇒≯ hx≤hy)
    
  abstract
  
    dᵣⁱ : Route → Route → ℕ
    dᵣⁱ x y = hⁱ x ⊔ hⁱ y

    dᵣⁱ-cong : dᵣⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dᵣⁱ-cong {x} {y} {u} {v} x≈y u≈v = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)
  
    dᵣⁱ-sym : ∀ x y → dᵣⁱ x y ≡ dᵣⁱ y x
    dᵣⁱ-sym x y = ⊔-comm (hⁱ x) (hⁱ y)

    dᵣⁱ≡0⇒x≈y : ∀ {x y} → dᵣⁱ x y ≡ 0 → x ≈ y
    dᵣⁱ≡0⇒x≈y {x} {y} dᵣⁱ≡0 = contradiction dᵣⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))
    
    dᵣⁱ-maxTriIneq : MaxTriangleIneq dᵣⁱ
    dᵣⁱ-maxTriIneq x y z = begin
      hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
      hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
      (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎
      where open ≤-Reasoning

    dᵣⁱ≤Hⁱ : ∀ x y → dᵣⁱ x y ≤ Hⁱ
    dᵣⁱ≤Hⁱ x y = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)
  
    dᵣⁱ-bounded : Bounded dᵣⁱ
    dᵣⁱ-bounded = Hⁱ , dᵣⁱ≤Hⁱ

    dᵣⁱ-mono-𝑰𝑪 : ∀ {w x y z} → 𝑪 w → 𝑪 x → 𝑰 y ⊎ 𝑰 z → dᵣⁱ w x < dᵣⁱ y z
    dᵣⁱ-mono-𝑰𝑪 {w} {x} {y} {z} wᶜ xᶜ yⁱ⊎zⁱ =
      m<n⊎m<o⇒m<n⊔o (hⁱ y) (hⁱ z)
        (map
        (λ yⁱ → n≤m×o≤m⇒n⊔o≤m (h[sᶜ]<h[rⁱ] wᶜ yⁱ) (h[sᶜ]<h[rⁱ] xᶜ yⁱ))
        (λ zⁱ → n≤m×o≤m⇒n⊔o≤m (h[sᶜ]<h[rⁱ] wᶜ zⁱ) (h[sᶜ]<h[rⁱ] xᶜ zⁱ))
        yⁱ⊎zⁱ)
      
    flip-< : ∀ {w x y z} → dᵣⁱ w x < dᵣⁱ y z → dᵣⁱ x w < dᵣⁱ z y
    flip-< dᵣⁱwx≤dᵣⁱyz = subst₂ _<_ (dᵣⁱ-sym _ _) (dᵣⁱ-sym _ _) dᵣⁱwx≤dᵣⁱyz 

    flip-≤ : ∀ {w x y z} → dᵣⁱ w x ≤ dᵣⁱ y z → dᵣⁱ x w ≤ dᵣⁱ z y
    flip-≤ dᵣⁱwx≤dᵣⁱyz = subst₂ _≤_ (dᵣⁱ-sym _ _) (dᵣⁱ-sym _ _) dᵣⁱwx≤dᵣⁱyz

    
    
    dᵣⁱ-strContr-lem : ∀ {i j r s} {X Y : RMatrix} → 𝑰 (σ X i j) →
                        hⁱ (σ Y i j) ≤ hⁱ (σ X i j) →
                        (∀ k l → 𝑰 (X k l) ⊎ 𝑰 (Y k l) → dᵣⁱ (X k l) (Y k l) ≤ dᵣⁱ (X r s) (Y r s)) →
                        hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) < hⁱ (X r s) ⊔ hⁱ (Y r s)
    dᵣⁱ-strContr-lem {i} {j} {r} {s} {X} {Y} σXᵢⱼⁱ hσYᵢⱼ≤hσXᵢⱼ less
      with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ          = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ
    ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
      hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) ≡⟨ n≤m⇒m⊔n≡m hσYᵢⱼ≤hσXᵢⱼ ⟩
      hⁱ (σ X i j)                ≡⟨ hⁱ-cong σXᵢⱼ≈AᵢₖXₖⱼ ⟩
      hⁱ (A i k ▷ X k j)          <⟨ hⁱ-decr (𝑰-cong σXᵢⱼ≈AᵢₖXₖⱼ σXᵢⱼⁱ) ⟩
      hⁱ (X k j)                  ≤⟨ m≤m⊔n (hⁱ (X k j)) (hⁱ (Y k j)) ⟩
      hⁱ (X k j) ⊔ hⁱ (Y k j)     ≤⟨ less k j (inj₁ (▷-forces-𝑰 (𝑰-cong σXᵢⱼ≈AᵢₖXₖⱼ σXᵢⱼⁱ))) ⟩
      hⁱ (X r s) ⊔ hⁱ (Y r s)     ∎
      where open ≤-Reasoning

{-
      D (σ X) (σ Y)                      ≡⟨ D≡dᵢⱼ ⟩ 
      d (σ X i j) (σ Y i j)              ≤⟨ d-mono σXᵢⱼ≤σYᵢⱼ (σXᵢⱼ≤Aᵢₖ▷Yₖⱼ k , σXᵢⱼ≉Aᵢₖ▷Yₖⱼ k) ⟩
      d (σ X i j) (A i k ▷ Y k j)        ≡⟨ d-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ≈-refl ⟩
      d (A i k ▷ X k j) (A i k ▷ Y k j)  <⟨ d-strContr (A i k) (Xₖⱼ≉Yₖⱼ σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) ⟩
      d (X k j) (Y k j)                  ≤⟨ d≤D X Y k j ⟩
      D X Y                              ∎
      -}
      
    dᵣⁱ-strContr : ∀ {i j r s X Y} → 𝑰 (σ X i j) ⊎ 𝑰 (σ Y i j) →
                   (∀ k l → 𝑰 (X k l) ⊎ 𝑰 (Y k l) → dᵣⁱ (X k l) (Y k l) ≤ dᵣⁱ (X r s) (Y r s)) → 
                   dᵣⁱ (σ X i j) (σ Y i j) < dᵣⁱ (X r s) (Y r s)
    dᵣⁱ-strContr {i} {j} {r} {s} {X} {Y} σXᵢⱼⁱ⊎σYᵢⱼⁱ less
      with ≤-total (hⁱ (σ X i j)) (hⁱ (σ Y i j))
    ...   | inj₂ σYᵢⱼ≤σXᵢⱼ = dᵣⁱ-strContr-lem (h-force-𝑰 (flip σXᵢⱼⁱ⊎σYᵢⱼⁱ) σYᵢⱼ≤σXᵢⱼ) σYᵢⱼ≤σXᵢⱼ less
    ...   | inj₁ σXᵢⱼ≤σYᵢⱼ =
      flip-< (dᵣⁱ-strContr-lem (h-force-𝑰 σXᵢⱼⁱ⊎σYᵢⱼⁱ σXᵢⱼ≤σYᵢⱼ) σXᵢⱼ≤σYᵢⱼ λ k l v → flip-≤ (less k l (flip v)))
  
