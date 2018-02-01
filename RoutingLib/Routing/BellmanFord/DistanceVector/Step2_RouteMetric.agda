open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst₂; module ≡-Reasoning)
open import Data.List using (List; _∷_)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_; _≤_; _≥_; _<_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; <⇒≢; <⇒≤; <⇒≱; ≤+≢⇒<; ⊔-comm; ⊔-identityʳ; ⊔-mono-≤; ⊔-mono-<; ≤-total; ≤-reflexive; ≤-refl; ≤-trans)
open import Data.Product using (∃; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Function using (_∘_)
import Relation.Binary.PartialOrderReasoning as PO-Reasoning

open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.Matrix using (Matrix; zipWith; max⁺)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m≤n⇒m≤n⊔o; n≤m⇒m⊔n≡m; n≤m×o≤m⇒n⊔o≤m; n≢0⇒0<n; module ≤-Reasoning)
open import RoutingLib.Function.Metric using (Ultrametric; IsUltrametric; Bounded; MaxTriangleIneq)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1

module RoutingLib.Routing.BellmanFord.DistanceVector.Step2_RouteMetric
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where
  
  open Prelude 𝓡𝓟 𝓢𝓒
  open Step1 𝓡𝓟 𝓢𝓒 using
    ( h
    ; h-resp-≈
    --; h-cancel-≡
    ; h-resp-<
    ; 1≤h
    ; h≤H
    )

  abstract

    h-resp-≤ : h Preserves _≤₊_ ⟶ _≥_
    h-resp-≤ {u} {v} u≤v with u ≟ v
    ... | yes u≈v = ≤-reflexive (h-resp-≈ (≈-sym u≈v))
    ... | no  u≉v = <⇒≤ (h-resp-< (u≤v , u≉v))
    
    h[fx]<h[x] : ∀ e {x} → x ≉ 0# → h (e ▷ x) < h x
    h[fx]<h[x] e x≉0 = h-resp-< (⊕-almost-strictly-absorbs-▷ e x≉0)

    ----------------------------
    -- distance between two routes
    
    d : Route → Route → ℕ
    d x y with x ≟ y
    ... | yes _ = zero
    ... | no  _ = h x ⊔ h y

    d-cong : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    d-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
    ... | yes _   | yes _   = refl
    ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
    ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
    ... | no  _   | no  _   = cong₂ _⊔_ (h-resp-≈ x≈y) (h-resp-≈ u≈v)

    x≈y⇒d≡0 : ∀ {x y} → x ≈ y → d x y ≡ 0
    x≈y⇒d≡0 {x} {y} x≈y with x ≟ y
    ... | yes _   = refl
    ... | no  x≉y = contradiction x≈y x≉y

    d≡0⇒x≈y : ∀ {x y} → d x y ≡ 0 → x ≈ y
    d≡0⇒x≈y {x} {y} d≡0 with x ≟ y 
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction (sym d≡0) (<⇒≢ (m≤n⇒m≤n⊔o (h y) (1≤h x)))
    
    d-sym : ∀ x y → d x y ≡ d y x
    d-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _   = refl
    ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y 
    ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x 
    ... | no  _   | no  _   = ⊔-comm (h x) (h y)

    d-maxTriIneq : MaxTriangleIneq S d
    d-maxTriIneq x y z with x ≟ y | y ≟ z | x ≟ z
    ... | _       | _       | yes _  = z≤n
    ... | yes x≈y | yes y≈z | no x≉z = contradiction (≈-trans x≈y y≈z) x≉z
    ... | yes x≈y | no  _   | no _   = ≤-reflexive (cong₂ _⊔_ (h-resp-≈ x≈y) (refl {x = h z}))
    ... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))
    ... | no  _   | yes y≈z | no _   = begin
      h x ⊔ h z     ≡⟨ cong (h x ⊔_) (h-resp-≈ (≈-sym y≈z)) ⟩
      h x ⊔ h y     ≡⟨ sym (⊔-identityʳ _) ⟩
      h x ⊔ h y ⊔ 0 ∎     
      where open ≤-Reasoning


    dxy≡hx⊔hy : ∀ {x y} → x ≉ y → d x y ≡ h x ⊔ h y
    dxy≡hx⊔hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = refl

    σXᵢⱼ≉Iᵢⱼ : ∀ X {i j} x → i ≢ j → σ X i j <₊ x → σ X i j ≉ I i j
    σXᵢⱼ≉Iᵢⱼ X {i} {j} x i≢j (σXᵢⱼ≤x , σXᵢⱼ≉x) σXᵢⱼ≈Iᵢⱼ =
      σXᵢⱼ≉x (≤₊-antisym σXᵢⱼ≤x (begin
        x         ≤⟨ 0#-idₗ-⊕ _ ⟩
        0#        ≈⟨ ≈-sym (≈-reflexive (Iᵢⱼ≡0# (i≢j ∘ sym))) ⟩
        I i j     ≈⟨ ≈-sym σXᵢⱼ≈Iᵢⱼ ⟩
        σ X i j   ∎))
      where open PO-Reasoning ≤₊-poset
      
    d-strContr2-lemma : ∀ {X Y r s} →
                        (∀ u v → X u v ≉ Y u v → d (X u v) (Y u v) ≤ h (X r s) ⊔ h (Y r s)) →
                        ∀ {i j} → σ X i j <₊ σ Y i j →
                        h (σ X i j) ⊔ h (σ Y i j) < h (X r s) ⊔ h (Y r s)
    d-strContr2-lemma {X} {Y} {r} {s} d≤hXᵣₛ⊔hYᵣₛ {i} {j} (σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ)
      with i ≟𝔽 j
    ... | yes refl = contradiction (σXᵢᵢ≈σYᵢᵢ X Y i) σXᵢⱼ≉σYᵢⱼ
    ... | no  i≢j with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ...   | inj₂ σXᵢⱼ≈Iᵢⱼ = contradiction σXᵢⱼ≈Iᵢⱼ (σXᵢⱼ≉Iᵢⱼ X (σ Y i j) i≢j ((σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ)))
        where open PO-Reasoning ≤₊-poset
    ...   | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) = begin
      h (σ X i j) ⊔ h (σ Y i j)   ≡⟨ n≤m⇒m⊔n≡m (h-resp-≤ σXᵢⱼ≤σYᵢⱼ) ⟩
      h (σ X i j)                 ≡⟨ h-resp-≈ σXᵢⱼ≈AᵢₖXₖⱼ ⟩
      h (A i k ▷ X k j)           <⟨ h-resp-< (⊕-almost-strictly-absorbs-▷ (A i k) Xₖⱼ≉0) ⟩
      h (X k j)                   ≤⟨ m≤m⊔n (h (X k j)) (h (Y k j)) ⟩
      h (X k j) ⊔ h (Y k j)       ≡⟨ sym (dxy≡hx⊔hy Xₖⱼ≉Yₖⱼ) ⟩
      d (X k j) (Y k j)           ≤⟨ d≤hXᵣₛ⊔hYᵣₛ k j Xₖⱼ≉Yₖⱼ ⟩
      h (X r s) ⊔ h (Y r s)     ∎
      where

      Xₖⱼ≉0 : X k j ≉ 0#
      Xₖⱼ≉0 Xₖⱼ≈0# = σXᵢⱼ≉σYᵢⱼ (≤₊-antisym σXᵢⱼ≤σYᵢⱼ (begin
        σ Y i j       ≤⟨ 0#-idₗ-⊕ _ ⟩
        0#            ≈⟨ ≈-sym (0#-an-▷ (A i k)) ⟩
        A i k ▷ 0#    ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈0#) ⟩
        A i k ▷ X k j ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
        σ X i j       ∎))
        where open PO-Reasoning ≤₊-poset
        
      Xₖⱼ≉Yₖⱼ : X k j ≉ Y k j
      Xₖⱼ≉Yₖⱼ Xₖⱼ≈Yₖⱼ = σXᵢⱼ≉σYᵢⱼ (≤₊-antisym σXᵢⱼ≤σYᵢⱼ (begin
        σ Y i j       ≤⟨ σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k ⟩
        A i k ▷ Y k j ≈⟨ ▷-cong (A i k) (≈-sym Xₖⱼ≈Yₖⱼ) ⟩
        A i k ▷ X k j ≈⟨ ≈-sym σXᵢⱼ≈AᵢₖXₖⱼ ⟩
        σ X i j       ∎))
        where open PO-Reasoning ≤₊-poset
        
      open ≤-Reasoning


    d-strContr : ∀ {X Y r s} → X r s ≉ Y r s →
                  (∀ u v → X u v ≉ Y u v → d (X u v) (Y u v) ≤ d (X r s) (Y r s)) →
                  ∀ i j → d (σ X i j) (σ Y i j) < d (X r s) (Y r s)
    d-strContr {X} {Y} {r} {s} Xᵣₛ≉Yᵣₛ d≤dXᵣₛYᵣₛ i j with X r s ≟ Y r s | σ X i j ≟ σ Y i j
    ... | yes Xᵣₛ≈Yᵣₛ | _            = contradiction Xᵣₛ≈Yᵣₛ Xᵣₛ≉Yᵣₛ
    ... | no  _      | yes σXᵢⱼ≈σYᵢⱼ = m≤n⇒m≤n⊔o (h (Y r s)) (1≤h (X r s))
    ... | no  _      | no  σXᵢⱼ≉σYᵢⱼ with ≤₊-total (σ X i j) (σ Y i j)
    ...   | inj₁ σXᵢⱼ≤σYᵢⱼ = d-strContr2-lemma d≤dXᵣₛYᵣₛ (σXᵢⱼ≤σYᵢⱼ , σXᵢⱼ≉σYᵢⱼ)
    ...   | inj₂ σXᵢⱼ≤σYᵢⱼ = begin
      h (σ X i j) ⊔ h (σ Y i j) ≡⟨ ⊔-comm (h (σ X i j)) (h (σ Y i j)) ⟩
      h (σ Y i j) ⊔ h (σ X i j) <⟨ d-strContr2-lemma d≤dYᵣₛXᵣₛ (σXᵢⱼ≤σYᵢⱼ , (σXᵢⱼ≉σYᵢⱼ ∘ ≈-sym)) ⟩
      h (Y r s)   ⊔ h (X r s)   ≡⟨ ⊔-comm (h (Y r s)) (h (X r s)) ⟩
      h (X r s)   ⊔ h (Y r s)   ∎
      where
      open ≤-Reasoning

      d≤dYᵣₛXᵣₛ : ∀ u v → Y u v ≉ X u v → d (Y u v) (X u v) ≤ h (Y r s) ⊔ h (X r s)
      d≤dYᵣₛXᵣₛ u v Yᵤᵥ≉Xᵤᵥ
        rewrite d-sym (Y u v) (X u v) | ⊔-comm (h (Y r s)) (h (X r s))
        = d≤dXᵣₛYᵣₛ u v (Yᵤᵥ≉Xᵤᵥ ∘ ≈-sym)

    d≤H : ∀ x y → d x y ≤ H
    d≤H x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = n≤m×o≤m⇒n⊔o≤m (h≤H x) (h≤H y)

    d-bounded : Bounded S d
    d-bounded = H , d≤H
    
    d-isUltrametric : IsUltrametric S d
    d-isUltrametric = record 
      { eq⇒0        = x≈y⇒d≡0 
      ; 0⇒eq        = d≡0⇒x≈y 
      ; sym         = d-sym 
      ; maxTriangle = d-maxTriIneq
      ; cong        = d-cong
      }

  d-ultrametric : Ultrametric S
  d-ultrametric = record
    { d             = d
    ; isUltrametric = d-isUltrametric
    }
