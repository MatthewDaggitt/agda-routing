open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Data.List using (List; _∷_)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _⊔_) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n; <⇒≢; ⊔-comm; ⊔-identityʳ; ⊔-mono-≤; module ≤-Reasoning) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-antisym to ≤ℕ-antisym; ≤-decTotalOrder to ≤ℕ-decTotalOrder)
open import Data.Product using (∃)

open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Sorting using (Sorted)
open import RoutingLib.Data.Matrix using (Matrix; zipWith; max⁺)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m≤n⇒m≤n⊔o)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)

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
    ; 1≤h
    ; h-image
    ; h-image!
    ; h-image-complete
    ; h-image-sound
    ; h-image↗
    )

  abstract
  
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
    ... | yes x≈y | no  _   | no _   = ≤ℕ-reflexive (cong₂ _⊔_ (h-resp-≈ x≈y) (refl {x = h z}))
    ... | no  _   | no  _   | no _   = ⊔-mono-≤ (m≤m⊔n (h x) (h y)) (n≤m⊔n (h y) (h z))
    ... | no  _   | yes y≈z | no _   = begin
      h x ⊔ h z     ≡⟨ cong (h x ⊔_) (h-resp-≈ (≈-sym y≈z)) ⟩
      h x ⊔ h y     ≡⟨ sym (⊔-identityʳ _) ⟩
      h x ⊔ h y ⊔ 0 ∎     
      where open ≤-Reasoning





    -- We can therefore reconstruct the image of d

    postulate d-image : List ℕ
    --d-image = 0 ∷ h-image
    
    postulate d-image! : Unique d-image
    --d-image! = {!!}

    postulate d-image-complete : ∀ x y → d x y ∈ d-image
    --d-image-complete x = {!!}

    postulate d-image-sound : ∀ {i} → i ∈ d-image → ∃ λ x → h x ≡ i
    --d-image-sound {i} i∈betw = {!!}

    postulate d-image↗ : Sorted ≤ℕ-decTotalOrder d-image
    --d-image↗ = {!!}
    

{-
    d-strContr : ∀ {x y} e → e ▷ x ≉ e ▷ y → d (e ▷ x) (e ▷ y) <ℕ d x y
    d-strContr {x} {y} e e▷x≉e▷y with x ≟ y | e ▷ x ≟ e ▷ y
    ... | yes x≈y | _           = contradiction {!!} e▷x≉e▷y
    ... | no  _   | yes e▷x≈e▷y = contradiction e▷x≈e▷y e▷x≉e▷y
    ... | no  _   | no  _       = {!⊔-mono-< ? ?!}
-}

{-
    d≤H : ∀ x y → d x y ≤ℕ H
    d≤H x y with x ≟ y
    ... | yes _ = z≤n
    ... | no  _ = {!!} --invert<dₘₐₓ x y

    x≉y⇒d≡invert : ∀ {x y} → x ≉ y → d x y ≡ h x ⊔ h y
    x≉y⇒d≡invert {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = refl

    d≢1 : ∀ x y → d x y ≢ 1
    d≢1 x y d≡1 with x ≟ y
    ... | yes x≈y = contradiction d≡1 λ()
    ... | no  x≉y = contradiction {!!} x≉y --(invert≡1⇒x≈y d≡1) x≉y

    Dₛᵤₚ∸hx≤d : ∀ {x y} → x ≉ y → Dₛᵤₚ ∸ h x ≤ℕ d x y
    Dₛᵤₚ∸hx≤d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = m≤m⊔n (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)

    Dₛᵤₚ∸hy≤d : ∀ {x y} → x ≉ y → Dₛᵤₚ ∸ h y ≤ℕ d x y
    Dₛᵤₚ∸hy≤d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = n≤m⊔n (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)
    
    d≡Dₛᵤₚ∸hx⇒hx≤hy : ∀ {x y} → d x y ≡ Dₛᵤₚ ∸ h x → h x ≤ℕ h y
    d≡Dₛᵤₚ∸hx⇒hx≤hy {x} {y} d≡dₘₐₓ∸hx with x ≟ y
    ... | yes x≈y = contradiction (trans d≡dₘₐₓ∸hx (+-∸-assoc 1 h≤hₘₐₓ)) λ()
    ... | no  x≉y = o∸n≤o∸m∧m≤o⇒m≤n (m⊔n≡m⇒n≤m d≡dₘₐₓ∸hx) h≤Dₛᵤₚ

    d≡Dₛᵤₚ∸hx : ∀ {x y} → h x <ℕ h y → d x y ≡ Dₛᵤₚ ∸ h x
    d≡Dₛᵤₚ∸hx {x} {y} hx<hy with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ x≈y) (<⇒≢ hx<hy)
    ... | no  x≉y = n≤m⇒m⊔n≡m (∸-mono (≤ℕ-refl {Dₛᵤₚ}) (<⇒≤ hx<hy))

    d≡Dₛᵤₚ∸hy : ∀ {x y} → h y <ℕ h x → d x y ≡ Dₛᵤₚ ∸ h y
    d≡Dₛᵤₚ∸hy {x} {y} hy<hx with x ≟ y
    ... | yes x≈y = contradiction (h-resp-≈ (≈-sym x≈y)) (<⇒≢ hy<hx)
    ... | no  x≉y = m≤n⇒m⊔n≡n (∸-mono (≤ℕ-refl {Dₛᵤₚ}) (<⇒≤ hy<hx))
    
    dxy=hx⊎hy : ∀ {x y} → x ≉ y → (d x y ≡ Dₛᵤₚ ∸ h x) ⊎ (d x y ≡ Dₛᵤₚ ∸ h y)
    dxy=hx⊎hy {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-sel (Dₛᵤₚ ∸ h x) (Dₛᵤₚ ∸ h y)

    x≉y⇒0<d : ∀ {x y} → x ≉ y → 0 <ℕ d x y
    x≉y⇒0<d {x} {y} x≉y with x ≟ y
    ... | yes x≈y = contradiction x≈y x≉y
    ... | no  _   = ⊔-mono-≤ 0<Dₛᵤₚ∸h 0<Dₛᵤₚ∸h
    
    0<d⇒x≉y : ∀ {x y} → 0 <ℕ d x y → x ≉ y
    0<d⇒x≉y {x} {y} 0<d with x ≟ y 
    ... | yes x≈yⱼ = contradiction 0<d 1+n≰n 
    ... | no  x≉y = x≉y

    

    
    -}
{-
    -----------------
    -- Ultrametric --
    -----------------
    -- We have now shown that d is an ultrametric

    D-isUltrametric : IsUltrametric ℝ𝕄ₛ D
    D-isUltrametric = record 
      { eq⇒0        = X≈Y⇒D≡0 
      ; 0⇒eq        = D≡0⇒X≈Y 
      ; sym         = D-sym 
      ; maxTriangle = D-maxTriIneq 
      }
-}
