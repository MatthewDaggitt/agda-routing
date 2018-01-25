open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _⊔_)
open import Data.Nat.Properties
  using (≤-reflexive; ≤-total; ⊔-comm; ⊔-identityʳ; m≤m⊔n)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Data.Nat.Properties
  using (⊔-monoˡ-≤; ⊔-triangulate; m≤o⇒m≤n⊔o; m<n⇒n≢0; n≤m×o≤m⇒n⊔o≤m; n≤m⇒m⊔n≡m;
        module ≤-Reasoning; ≤⇒≯)
import RoutingLib.Function.Distance as Distance 

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

    h-force-𝑰 : ∀ {x y} → hⁱ x ≤ hⁱ y → 𝑰 x → 𝑰 y
    h-force-𝑰 hx≤hy xⁱ yᶜ = contradiction (h[sᶜ]<h[rⁱ] yᶜ xⁱ) (≤⇒≯ hx≤hy)
  
  abstract
  
    dᵣⁱ : Route → Route → ℕ
    dᵣⁱ x y with x ≟ y
    ... | yes _ = 0
    ... | no  _ = hⁱ x ⊔ hⁱ y

    dᵣⁱ-cong : dᵣⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dᵣⁱ-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
    ... | yes _   | yes _   = refl
    ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
    ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
    ... | no  _   | no  _   = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)
  
    dᵣⁱ-sym : ∀ x y → dᵣⁱ x y ≡ dᵣⁱ y x
    dᵣⁱ-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _ = refl
    ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
    ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
    ... | no  _   | no  _   = ⊔-comm (hⁱ x) (hⁱ y)

    dᵣⁱ≡0⇒x≈y : ∀ {x y} → dᵣⁱ x y ≡ 0 → x ≈ y
    dᵣⁱ≡0⇒x≈y {x} {y} dᵣⁱ≡0 with x ≟ y
    ... | yes x≈y = x≈y
    ... | no  x≉y = contradiction dᵣⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))
  
    x≈y⇒dᵣⁱ≡0 : ∀ {x y} → x ≈ y → dᵣⁱ x y ≡ 0
    x≈y⇒dᵣⁱ≡0 {x} {y} x≈y with x ≟ y
    ... | yes _   = refl
    ... | no  x≉y = contradiction x≈y x≉y
  
    dᵣⁱ-maxTriIneq : MaxTriangleIneq dᵣⁱ
    dᵣⁱ-maxTriIneq x y z with x ≟ z | x ≟ y | y ≟ z
    ... | yes _   | _       | _       = z≤n
    ... | no  x≉z | yes x≈y | yes y≈z = contradiction (≈-trans x≈y y≈z) x≉z
    ... | no  _   | yes x≈y | no  _   = ≤-reflexive (cong (_⊔ hⁱ z) (hⁱ-cong x≈y))
    ... | no  _   | no  _   | yes y≈z = ≤-reflexive (trans (cong (hⁱ x ⊔_) (sym (hⁱ-cong y≈z))) (sym (⊔-identityʳ _)))
    ... | no  _   | no  _   | no  _   = begin
      hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
      hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
      (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎
      where open ≤-Reasoning
  
    dᵣⁱ-isUltrametric : IsUltrametric dᵣⁱ
    dᵣⁱ-isUltrametric = record
      { cong        = dᵣⁱ-cong
      ; eq⇒0        = x≈y⇒dᵣⁱ≡0
      ; 0⇒eq        = dᵣⁱ≡0⇒x≈y
      ; sym         = dᵣⁱ-sym
      ; maxTriangle = dᵣⁱ-maxTriIneq
      }

    dᵣⁱ≤Hⁱ : ∀ x y → dᵣⁱ x y ≤ Hⁱ
    dᵣⁱ≤Hⁱ x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)
  
    dᵣⁱ-bounded : Bounded dᵣⁱ
    dᵣⁱ-bounded = Hⁱ , dᵣⁱ≤Hⁱ






    dᵣⁱ-strContr-lemma : ∀ {i j k l x y} → 𝑰 (A i j ▷ x) →
                         hⁱ (A k l ▷ y) ≤ hⁱ (A i j ▷ x) →
                         hⁱ (A i j ▷ x) ⊔ hⁱ (A k l ▷ y) < hⁱ x ⊔ hⁱ y
    dᵣⁱ-strContr-lemma {i} {j} {k} {l} {x} {y} Axⁱ hAy≤hAx = begin
      hⁱ (A i j ▷ x) ⊔ hⁱ (A k l ▷ y)  ≡⟨ n≤m⇒m⊔n≡m hAy≤hAx ⟩
      hⁱ (A i j ▷ x)                   <⟨ hⁱ-decr Axⁱ ⟩
      hⁱ x                             ≤⟨ m≤m⊔n (hⁱ x) (hⁱ y) ⟩
      hⁱ x       ⊔ hⁱ y                ∎
      where open ≤-Reasoning

    dᵣⁱ-strContr : ∀ {i j k l x y} → x ≉ y → 𝑰 (A i j ▷ x) ⊎ 𝑰 (A k l ▷ y) →
                   dᵣⁱ (A i j ▷ x) (A k l ▷ y) < dᵣⁱ x y
    dᵣⁱ-strContr {i} {j} {k} {l} {x} {y} x≉y Axⁱ⊎Ayⁱ with x ≟ y | A i j ▷ x ≟ A k l ▷ y
    ... | yes x≈y | _     = contradiction x≈y x≉y
    ... | no  _   | yes _ = m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)
    ... | no  _   | no  _ with ≤-total (hⁱ (A i j ▷ x)) (hⁱ (A k l ▷ y))
    ...   | inj₂ hAy≤hAx = dᵣⁱ-strContr-lemma ([ id , h-force-𝑰 hAy≤hAx ]′ Axⁱ⊎Ayⁱ) hAy≤hAx
    ...   | inj₁ hAx≤hAy = begin
      hⁱ (A i j ▷ x) ⊔ hⁱ (A k l ▷ y) ≡⟨ ⊔-comm (hⁱ (A i j ▷ x)) (hⁱ (A k l ▷ y)) ⟩
      hⁱ (A k l ▷ y) ⊔ hⁱ (A i j ▷ x) <⟨ dᵣⁱ-strContr-lemma ([ h-force-𝑰 hAx≤hAy , id ]′ Axⁱ⊎Ayⁱ) hAx≤hAy ⟩
      hⁱ y       ⊔ hⁱ x               ≡⟨ ⊔-comm (hⁱ y) (hⁱ x) ⟩
      hⁱ x       ⊔ hⁱ y               ∎
      where open ≤-Reasoning





{-
    dᵣⁱ-strContr2-lem : ∀ {i j r s} {X Y : RMatrix} → 𝑰 (σ X i j) →
                        hⁱ (σ Y i j) ≤ hⁱ (σ X i j) →
                        (∀ k l → hⁱ (X k l) ⊔ hⁱ (Y k l) ≤ hⁱ (X r s) ⊔ hⁱ (Y r s)) →
                        hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) < hⁱ (X r s) ⊔ hⁱ (Y r s)
    dᵣⁱ-strContr2-lem {i} {j} {r} {s} {X} {Y} σXᵢⱼⁱ hσYᵢⱼ≤hσXᵢⱼ less
      with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ          = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ
    ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
      hⁱ (σ X i j) ⊔ hⁱ (σ Y i j) ≡⟨ n≤m⇒m⊔n≡m hσYᵢⱼ≤hσXᵢⱼ ⟩
      hⁱ (σ X i j)                ≡⟨ hⁱ-cong σXᵢⱼ≈AᵢₖXₖⱼ ⟩
      hⁱ (A i k ▷ X k j)          <⟨ hⁱ-decr (𝑰-cong σXᵢⱼ≈AᵢₖXₖⱼ σXᵢⱼⁱ) ⟩
      hⁱ (X k j)                  ≤⟨ m≤m⊔n (hⁱ (X k j)) (hⁱ (Y k j)) ⟩
      hⁱ (X k j) ⊔ hⁱ (Y k j)     ≤⟨ less k j ⟩
      hⁱ (X r s) ⊔ hⁱ (Y r s)     ∎
      where open ≤-Reasoning

    dᵣⁱ-strContr2 : ∀ {i j r s X Y} → X r s ≉ Y r s → σ X i j ≉ σ Y i j →
                   𝑰 (σ X i j) ⊎ 𝑰 (σ Y i j) →
                   (∀ k l → dᵣⁱ (X k l) (Y k l) < dᵣⁱ (X r s) (Y r s)) → 
                   dᵣⁱ (σ X i j) (σ Y i j) < dᵣⁱ (X r s) (Y r s)
    dᵣⁱ-strContr2 {i} {j} {r} {s} {X} {Y} Xᵣₛ≉Yᵣₛ σXᵢⱼ≉σYᵢⱼ σXᵢⱼⁱ⊎σYᵢⱼⁱ less
      with X r s ≟ Y r s | σ X i j ≟ σ Y i j
    ... | yes Xᵣₛ≈Yᵣₛ | _            = contradiction Xᵣₛ≈Yᵣₛ Xᵣₛ≉Yᵣₛ
    ... | _          | yes σXᵢⱼ≈σYᵢⱼ = contradiction σXᵢⱼ≈σYᵢⱼ σXᵢⱼ≉σYᵢⱼ
    ... | no  _      | no  _
        with σXᵢⱼⁱ⊎σYᵢⱼⁱ | ≤-total (hⁱ (σ X i j)) (hⁱ (σ Y i j))
    ...   | inj₁ σXᵢⱼⁱ | inj₁ σXᵢⱼ≤σYᵢⱼ = {!!}
    ...   | inj₁ σXᵢⱼⁱ | inj₂ σYᵢⱼ≤σXᵢⱼ = dᵣⁱ-strContr2-lem σXᵢⱼⁱ σYᵢⱼ≤σXᵢⱼ {!!}
    ...   | inj₂ σYᵢⱼⁱ | inj₁ σXᵢⱼ≤σYᵢⱼ = {!!}
    ...   | inj₂ σYᵢⱼⁱ | inj₂ σYᵢⱼ≤σXᵢⱼ = {!!}
 -}




  dᵣⁱ-ultrametric : Ultrametric
  dᵣⁱ-ultrametric = record
    { d             = dᵣⁱ
    ; isUltrametric = dᵣⁱ-isUltrametric
    }

  
