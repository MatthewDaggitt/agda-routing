open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; map; swap)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _⊔_)
open import Data.Nat.Properties
  using (≤-refl; ≤-reflexive; ≤-total; <-transˡ; <-transʳ; ⊔-comm; ⊔-identityʳ; ⊔-idem; m≤m⊔n; <⇒≯; <⇒≤; n≤m⊔n; ≤⇒≯; ⊔-monoˡ-≤; m≤n⇒m⊔n≡n; m≤n⇒n⊔m≡n; ⊔-triangulate)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⁅_⁆; ∣_∣; ⊤)
open import Data.Fin.Subset.Properties using (x∈p∩q⁺; x∈⁅x⁆; ∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wellFounded)

open import RoutingLib.Data.Fin.Subset using (_\\_)
open import RoutingLib.Data.Fin.Subset.Properties using (∣p\\q∣<∣p∣; i∉p\\q⇒i∉p; i∉⁅j⁆)
open import RoutingLib.Data.Nat.Properties
  using (m≤o⇒m≤n⊔o; m<n⇒n≢0; n≤m×o≤m⇒n⊔o≤m; m<n⊎m<o⇒m<n⊔o; m≤n⇒m≤n⊔o; module ≤-Reasoning)
import RoutingLib.Function.Metric as Metric

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Step1_InconsistentHeightFunction as Step1

module RoutingLib.Routing.BellmanFord.AsyncConvergence.PathVector.Step2_InconsistentRouteMetric
  {a b ℓ n} (algebra : StrictlyIncreasingPathAlgebra a b ℓ n)
  where

  open Prelude algebra
  open Step1 algebra using
    ( hⁱ ; Hⁱ ; hⁱ-cong ; 1≤hⁱ; hⁱ≤Hⁱ ; hⁱ-decr ; h[sᶜ]<h[rⁱ] )
 
  open Metric S

  open ≤-Reasoning
    
  private

    h-force-𝑰 : ∀ {x y} → 𝑰 x ⊎ 𝑰 y → hⁱ x ≤ hⁱ y → 𝑰 y
    h-force-𝑰 (inj₂ yⁱ) hx≤hy yᶜ = yⁱ yᶜ
    h-force-𝑰 (inj₁ xⁱ) hx≤hy yᶜ = contradiction (h[sᶜ]<h[rⁱ] yᶜ xⁱ) (≤⇒≯ hx≤hy)
    
  abstract
  
    dᵣⁱ : Route → Route → ℕ
    dᵣⁱ x y = hⁱ x ⊔ hⁱ y

    dᵣⁱ-cong : dᵣⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dᵣⁱ-cong x≈y u≈v = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)
  
    dᵣⁱ-sym : ∀ x y → dᵣⁱ x y ≡ dᵣⁱ y x
    dᵣⁱ-sym x y = ⊔-comm (hⁱ x) (hⁱ y)

    dᵣⁱ≡0⇒x≈y : ∀ {x y} → dᵣⁱ x y ≡ 0 → x ≈ y
    dᵣⁱ≡0⇒x≈y {x} {y} dᵣⁱ≡0 = contradiction dᵣⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))
    
    dᵣⁱ-maxTriIneq : MaxTriangleIneq dᵣⁱ
    dᵣⁱ-maxTriIneq x y z = begin
      hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
      hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
      (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎

    1≤dᵣⁱ : ∀ x y → 1 ≤ dᵣⁱ x y
    1≤dᵣⁱ x y = m≤n⇒m≤n⊔o (hⁱ y) (1≤hⁱ x)
    
    dᵣⁱ≤Hⁱ : ∀ x y → dᵣⁱ x y ≤ Hⁱ
    dᵣⁱ≤Hⁱ x y = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)
  
    dᵣⁱ-bounded : Bounded dᵣⁱ
    dᵣⁱ-bounded = Hⁱ , dᵣⁱ≤Hⁱ
    

    
    private
    
      

      chain₁ : ∀ X i j → 𝑰 (σ X i j) → ∃ λ k → 𝑰 (X k j) × hⁱ (σ X i j) < hⁱ (X k j) ⊔ hⁱ (σ X k j)
      chain₁ X i j σXᵢⱼⁱ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X _ _ σXᵢⱼⁱ
      ... | k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ , Xₖⱼⁱ = k , Xₖⱼⁱ , (begin
        hⁱ (σ X i j)              ≡⟨ hⁱ-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ ⟩
        hⁱ (A i k ▷ X k j)        <⟨ hⁱ-decr (𝑰-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ σXᵢⱼⁱ) ⟩
        hⁱ (X k j)                ≤⟨ m≤m⊔n (hⁱ (X k j)) (hⁱ (σ X k j)) ⟩
        hⁱ (X k j) ⊔ hⁱ (σ X k j) ∎)
        
      chain₂ : ∀ X i k j → hⁱ (σ X i j) < hⁱ (X k j) ⊔ hⁱ (σ X k j) → X k j ≈ σ X k j → hⁱ (σ X i j) < hⁱ (σ X k j)
      chain₂ X i k j hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ Xₖⱼ≈σXₖⱼ = begin
        hⁱ (σ X i j)                <⟨ hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ ⟩
        hⁱ (X k j)   ⊔ hⁱ (σ X k j) ≡⟨ cong (_⊔ hⁱ (σ X k j)) (hⁱ-cong Xₖⱼ≈σXₖⱼ) ⟩
        hⁱ (σ X k j) ⊔ hⁱ (σ X k j) ≡⟨ ⊔-idem (hⁱ (σ X k j)) ⟩
        hⁱ (σ X k j)                ∎
      
      reduction : ∀ X {r s} →
                  (∀ {u v} → X u v ≉ σ X u v → 𝑰 (X u v) ⊎ 𝑰 (σ X u v) → dᵣⁱ (X u v) (σ X u v) ≤ dᵣⁱ (X r s) (σ X r s)) →
                  ∀ i j (L : Subset n) → Acc _<_ ∣ L ∣ → (∀ {l} → l ∉ L → hⁱ (σ X l j) ≤ hⁱ (σ X i j)) →
                  𝑰 (σ X i j) → hⁱ (σ X i j) < hⁱ (X r s) ⊔ hⁱ (σ X r s)
      reduction X {r} {s} dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ i j L (acc rec) L-less σXᵢⱼⁱ with chain₁ X _ _ σXᵢⱼⁱ
      ... | k , Xₖⱼⁱ , hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ  with X k j ≟ σ X k j
      ...   | no  Xₖⱼ≉σXₖⱼ = <-transˡ (hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ) (dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ Xₖⱼ≉σXₖⱼ (inj₁ Xₖⱼⁱ))
      ...   | yes Xₖⱼ≈σXₖⱼ with chain₂ X i k j hσXᵢⱼ<hXₖⱼ⊔hσXₖⱼ Xₖⱼ≈σXₖⱼ | k ∈? L
      ...     | hσXᵢⱼ<hσXₖⱼ | no  k∉L = contradiction hσXᵢⱼ<hσXₖⱼ (≤⇒≯ (L-less k∉L))
      ...     | hσXᵢⱼ<hσXₖⱼ | yes k∈L = begin
        hⁱ (σ X i j)                <⟨ hσXᵢⱼ<hσXₖⱼ ⟩
        hⁱ (σ X k j)                <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ k j (L \\ ⁅ k ⁆) (rec _ ∣L\\k∣<∣L∣) L-exclude (𝑰-cong Xₖⱼ≈σXₖⱼ Xₖⱼⁱ) ⟩
        hⁱ (X r s) ⊔ hⁱ (σ X r s) ∎

        where
  
        ∣L\\k∣<∣L∣ : ∣ L \\ ⁅ k ⁆ ∣ < ∣ L ∣
        ∣L\\k∣<∣L∣ = ∣p\\q∣<∣p∣ {p = L} {⁅ k ⁆} (k , x∈p∩q⁺ (k∈L , x∈⁅x⁆ k))
  
        L-exclude : ∀ {l} → l ∉ (L \\ ⁅ k ⁆) → hⁱ (σ X l j) ≤ hⁱ (σ X k j)
        L-exclude {l} l∉L\\k with l ≟𝔽 k
        ... | yes refl = ≤-refl
        ... | no  l≢k  = <⇒≤ (<-transʳ (L-less (i∉p\\q⇒i∉p l∉L\\k (i∉⁅j⁆ l≢k))) hσXᵢⱼ<hσXₖⱼ)



    dᵣⁱ-strContrOrbits : ∀ X {r s} →
                   (∀ {u v} → X u v ≉ σ X u v → 𝑰 (X u v) ⊎ 𝑰 (σ X u v) → dᵣⁱ (X u v) (σ X u v) ≤ dᵣⁱ (X r s) (σ X r s)) → 
                   ∀ {i j} → 𝑰 (σ X i j) ⊎ 𝑰 (σ (σ X) i j) → dᵣⁱ (σ X i j) (σ (σ X) i j) < dᵣⁱ (X r s) (σ X r s)
    dᵣⁱ-strContrOrbits X {r} {s} dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ {i} {j} σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ with ≤-total (hⁱ (σ (σ X) i j)) (hⁱ (σ X i j))
    ...   | inj₁ σ²Xᵢⱼ≤σXᵢⱼ = begin
      hⁱ (σ X i j) ⊔ hⁱ (σ (σ X) i j) ≡⟨ m≤n⇒n⊔m≡n σ²Xᵢⱼ≤σXᵢⱼ ⟩
      hⁱ (σ X i j)                    <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ i j ⊤ (<-wellFounded ∣ ⊤ {n = n} ∣) (λ l∉⊤ → contradiction ∈⊤ l∉⊤) (h-force-𝑰 (swap σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ) σ²Xᵢⱼ≤σXᵢⱼ) ⟩
      hⁱ (X r s)   ⊔ hⁱ (σ X r s)     ∎
    ...   | inj₂ σXᵢⱼ≤σ²Xᵢⱼ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ (σ X) _ _ (h-force-𝑰 σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ σXᵢⱼ≤σ²Xᵢⱼ)
    ... | k , σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ , σXₖⱼⁱ = begin
      hⁱ (σ X i j) ⊔ hⁱ (σ (σ X) i j) ≡⟨ m≤n⇒m⊔n≡n σXᵢⱼ≤σ²Xᵢⱼ ⟩
      hⁱ (σ (σ X) i j)                ≡⟨ hⁱ-cong σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ ⟩
      hⁱ (A i k ▷ σ X k j)            <⟨ hⁱ-decr (𝑰-cong σ²Xᵢⱼ≈Aᵢₖ▷σXₖⱼ (h-force-𝑰 σXᵢⱼⁱ⊎σ²Xᵢⱼⁱ σXᵢⱼ≤σ²Xᵢⱼ)) ⟩
      hⁱ (σ X k j)                    <⟨ reduction X dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ k j ⊤ (<-wellFounded ∣ ⊤ {n = n} ∣) (λ l∉⊤ → contradiction ∈⊤ l∉⊤) σXₖⱼⁱ ⟩ 
      hⁱ (X r s)   ⊔ hⁱ (σ X r s)     ∎



    dᵣⁱxⁱyᶜ≡hⁱxⁱ : ∀ {x y} → 𝑰 x → 𝑪 y → dᵣⁱ x y ≡ hⁱ x
    dᵣⁱxⁱyᶜ≡hⁱxⁱ {x} {y} xⁱ yᶜ with x ≟ y
    ... | yes x≈y = contradiction (𝑪-cong (≈-sym x≈y) yᶜ) xⁱ
    ... | no  _   with 𝑪? x | 𝑪? y
    ...   | yes xᶜ | _      = contradiction xᶜ xⁱ
    ...   | no  _  | no yⁱ = contradiction yᶜ yⁱ
    ...   | no  _  | yes _ = m≤n⇒n⊔m≡n (<⇒≤ (h[sᶜ]<h[rⁱ] yᶜ xⁱ))
    
    xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy : ∀ {x y z} → 𝑰 x → 𝑪 y → 𝑪 z → dᵣⁱ x z ≤ dᵣⁱ x y
    xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy xⁱ yᶜ zᶜ =
      ≤-reflexive (trans (dᵣⁱxⁱyᶜ≡hⁱxⁱ xⁱ zᶜ) (sym (dᵣⁱxⁱyᶜ≡hⁱxⁱ xⁱ yᶜ)))
    
    xᶜyᶜzⁱ⇒dᵣⁱxz≤dᵣⁱyz : ∀ {x y z} → 𝑪 x → 𝑪 y → 𝑰 z → dᵣⁱ x z ≤ dᵣⁱ y z
    xᶜyᶜzⁱ⇒dᵣⁱxz≤dᵣⁱyz {x} {y} {z} xᶜ yᶜ zⁱ =
      subst₂ _≤_ (dᵣⁱ-sym z x) (dᵣⁱ-sym z y) (xⁱyᶜzᶜ⇒dᵣⁱxz≤dᵣⁱxy zⁱ yᶜ xᶜ)






    dᵣⁱ-strContrᶜ : ∀ X Y {r s} → 𝑪ₘ X →
                   (∀ {u v} → X u v ≉ Y u v → 𝑰 (X u v) ⊎ 𝑰 (Y u v) → dᵣⁱ (X u v) (Y u v) ≤ dᵣⁱ (X r s) (Y r s)) → 
                   ∀ {i j} → 𝑰 (σ Y i j) → dᵣⁱ (σ X i j) (σ Y i j) < dᵣⁱ (X r s) (Y r s)
    dᵣⁱ-strContrᶜ X Y {r} {s} Xᶜ dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ {i} {j} σYᵢⱼⁱ with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ Y _ _ σYᵢⱼⁱ
    ... | k , σYᵢⱼ≈Aᵢₖ▷Yₖⱼ , Yₖⱼⁱ = begin
      hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) ≡⟨ m≤n⇒m⊔n≡n (<⇒≤ (h[sᶜ]<h[rⁱ] (σ-pres-𝑪ₘ Xᶜ i j) σYᵢⱼⁱ)) ⟩
      hⁱ (σ Y i j)            ≡⟨ hⁱ-cong σYᵢⱼ≈Aᵢₖ▷Yₖⱼ ⟩
      hⁱ (A i k ▷ Y k j)      <⟨ hⁱ-decr (𝑰-cong σYᵢⱼ≈Aᵢₖ▷Yₖⱼ σYᵢⱼⁱ) ⟩
      hⁱ (Y k j)              ≤⟨ n≤m⊔n (hⁱ (X k j)) (hⁱ (Y k j)) ⟩
      hⁱ (X k j) ⊔ hⁱ (Y k j) ≤⟨ dᵣⁱ≤dᵣⁱXᵣₛYᵣₛ (Yₖⱼⁱ ∘ (λ Xₖⱼ≈Yₖⱼ → 𝑪-cong Xₖⱼ≈Yₖⱼ (Xᶜ k j))) (inj₂ Yₖⱼⁱ) ⟩
      hⁱ (X r s) ⊔ hⁱ (Y r s) ∎
