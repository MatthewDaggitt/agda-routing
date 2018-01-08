open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-step; ≤-steps; <⇒≤; <⇒≢; ≤+≢⇒<; ∸-mono; +-∸-assoc; n∸m≤n; n∸n≡0; ≤⇒pred≤; ≤-decTotalOrder; module ≤-Reasoning)  renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.List using (List; _∷_; drop; upTo)
open import Data.List.All using (All; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (All-universal)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning; inspect; [_])
  renaming (setoid to ≡-setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions)
open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using (SufficientConditions)
open import RoutingLib.Data.List.All using (_∷_)
open import RoutingLib.Data.List.All.Properties using (s≤betweenₛₑ; betweenₛₑ<e)
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.List.Uniqueness.Properties using (drop!⁺; upTo!⁺; between!⁺)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-upTo⁺; ∈-between⁺; ∈-between⁻)
open import RoutingLib.Data.List using (between)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
open import RoutingLib.Data.List.Sorting.Nat using (↗-between)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; m∸[m∸n]≡n; m<n⇒n≢0; m<n⇒n≡1+o; m∸n<o⇒m∸o<n)
open import RoutingLib.Data.Matrix using (Matrix; max⁺; map)
open import RoutingLib.Data.Matrix.Properties using (M≤max⁺[M])
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Function.Distance.Properties using (x*; x*-fixed)

import RoutingLib.Routing.BellmanFord.DistanceVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_Ultrametric as Step2
import RoutingLib.Routing.BellmanFord.DistanceVector.Step3_StrictlyContracting as Step3

module RoutingLib.Routing.BellmanFord.DistanceVector.Step4_AsynchronousConditions
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1))
  (𝓢𝓒 : SufficientConditions 𝓡𝓐)
  where

  open Prelude 𝓡𝓟 𝓢𝓒
  open Step1 𝓡𝓟 𝓢𝓒
  open Step2 𝓡𝓟 𝓢𝓒
  open Step3 𝓡𝓟 𝓢𝓒

  open import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 using (Iᵢⱼ≡0#)

  
  
  -- Z is the unique fixed point of σ
  
  Z : RMatrix
  Z = x* ℝ𝕄ₛ _≟ₘ_ D σ-strictlyContractingOnOrbits I
  
  Z-fixed : σ Z ≈ₘ Z
  Z-fixed = x*-fixed ℝ𝕄ₛ _≟ₘ_ D σ-strictlyContractingOnOrbits I

  -- Zₛₜ is the maximal element in Z with respect to the height function
  
  s : Fin n
  s with max⁺[M]∈M (map h Z)
  ... | i , _ , _ = i
  
  t : Fin n
  t with max⁺[M]∈M (map h Z)
  ... | _ , j , _ = j
  
  hZᵢⱼ≤hZₛₜ : ∀ i j → h (Z i j) ≤ℕ h (Z s t)
  hZᵢⱼ≤hZₛₜ i j with max⁺[M]∈M (map h Z)
  ... | _ , _ , hZₛₜ≡max⁺ = subst (h (Z i j) ≤ℕ_) hZₛₜ≡max⁺ (M≤max⁺[M] (map h Z) i j)


  -- As Zₛₜ is the maximal element we can define the minimal distance
  -- any matrix can be from Z (excluding Z itself)

  Dₘᵢₙ : ℕ
  Dₘᵢₙ with Z s t ≟ 0#
  ... | yes _ = 2
  ... | no  _ = Dₛᵤₚ ∸ h (Z s t)
  
  Dₘᵢₙ≤dXZ : ∀ {X} → X ≉ₘ Z → Dₘᵢₙ ≤ℕ D X Z
  Dₘᵢₙ≤dXZ {X} X≉Z with Z s t ≟ 0# | ≉ₘ-witness X≉Z
  ... | no  _      | i , j , Xᵢⱼ≉Zᵢⱼ = ≤ℕ-trans (∸-mono ≤ℕ-refl (hZᵢⱼ≤hZₛₜ i j)) (Dₛᵤₚ∸hYᵢⱼ≤D Xᵢⱼ≉Zᵢⱼ)
  ... | yes Zₛₜ≈0# | _              with D X Z | inspect (D X) Z
  ...   | zero        | [ DXZ≡0 ] = contradiction (D≡0⇒X≈Y DXZ≡0) X≉Z
  ...   | suc zero    | [ DXZ≡1 ] = contradiction DXZ≡1 (D≢1 X Z)
  ...   | suc (suc n) | _         = s≤s (s≤s z≤n)
  
  Dₘᵢₙ≤x⇒0≢x : {x : ℕ} → Dₘᵢₙ ≤ℕ x → 0 ≢ x
  Dₘᵢₙ≤x⇒0≢x {suc x} Dₘᵢₙ≤x ()
  Dₘᵢₙ≤x⇒0≢x {zero}  Dₘᵢₙ≤x with Z s t ≟ 0#
  ... | yes _ = contradiction Dₘᵢₙ≤x λ()
  ... | no  _ = contradiction (subst (_≤ℕ 0) (+-∸-assoc 1 h≤hₘₐₓ) Dₘᵢₙ≤x) λ()


  -- Z[ x ] is copy of matrix Z with Zₛₜ replaced with route x

  Z[_] : Route → RMatrix
  Z[ x ] i j with i ≟𝔽 s | j ≟𝔽 t
  ... | yes _ | yes _ = x
  ... | no  _ | _     = Z i j
  ... | _     | no  _ = Z i j

  Z[x]ᵢⱼ≡Zᵢⱼ : ∀ x {i j} → (i , j) ≢ (s , t) → Z[ x ] i j ≡ Z i j
  Z[x]ᵢⱼ≡Zᵢⱼ x {i} {j} ij≢st with i ≟𝔽 s | j ≟𝔽 t
  ... | yes refl | yes refl = contradiction refl ij≢st
  ... | no  _    | _        = refl
  ... | yes _    | no _     = refl

  Z[x]ₛₜ≡x : ∀ x → Z[ x ] s t ≡ x
  Z[x]ₛₜ≡x x with s ≟𝔽 s | t ≟𝔽 t
  ... | yes _     | yes _   = refl
  ... | no  s≢s   | _       = contradiction refl s≢s
  ... | yes _     | no  t≢t = contradiction refl t≢t

  dZᵢⱼ≤dZₛₜ : ∀ {x} → ∀ i j → d (Z[ x ] i j) (Z i j) ≤ℕ d (Z[ x ] s t) (Z s t)
  dZᵢⱼ≤dZₛₜ i j with i ≟𝔽 s | j ≟𝔽 t
  ... | no  _    | _        = subst (_≤ℕ _) (sym (x≈y⇒d≡0 ≈-refl)) z≤n
  ... | yes _    | no _     = subst (_≤ℕ _) (sym (x≈y⇒d≡0 ≈-refl)) z≤n
  ... | yes refl | yes refl with s ≟𝔽 s | t ≟𝔽 t
  ...   | no  s≢s   | _       = contradiction refl s≢s
  ...   | yes _     | no  t≢t = contradiction refl t≢t
  ...   | yes _     | yes _   = ≤ℕ-refl

  Zₛₜ<Z[0]ₛₜ : Z s t ≉ 0# → Z s t < Z[ 0# ] s t
  Zₛₜ<Z[0]ₛₜ Zₛₜ≉0# with s ≟𝔽 s | t ≟𝔽 t
  ... | yes _     | yes _   = 0#-idₗ-⊕ (Z s t) , Zₛₜ≉0#
  ... | no  s≢s   | _       = contradiction refl s≢s
  ... | yes _     | no  t≢t = contradiction refl t≢t

  ∃X⇒Dₛᵤₚ∸hZₛₜ : Z s t ≉ 0# →  ∃ λ X → D X Z ≡ Dₛᵤₚ ∸ h (Z s t)
  ∃X⇒Dₛᵤₚ∸hZₛₜ Zₛₜ≉0# = Z[ 0# ] , D≡Dₛᵤₚ∸Yᵢⱼ dZᵢⱼ≤dZₛₜ (h-resp-< (Zₛₜ<Z[0]ₛₜ Zₛₜ≉0#))
  
  test : ∀ {i} → Dₛᵤₚ ∸ h (Z s t) <ℕ i → i <ℕ Dₛᵤₚ → ∃ λ X → D X Z ≡ i 
  test {i} Dₛᵤₚ∸hZₛₜ<i i<Dₛᵤₚ with m<n⇒n≡1+o Dₛᵤₚ∸hZₛₜ<i
  ... | (i-1 , refl) = Z[ x ] , (begin
    D Z[ x ] Z            ≡⟨ D≡Dₛᵤₚ∸Xᵢⱼ dZᵢⱼ≤dZₛₜ hZ[x]ₛₜ<hZₛₜ ⟩
    Dₛᵤₚ ∸ h (Z[ x ] s t) ≡⟨ cong (Dₛᵤₚ ∸_) hZ[x]ₛₜ≡Dₛᵤₚ∸i ⟩
    Dₛᵤₚ ∸ (Dₛᵤₚ ∸ i)     ≡⟨ m∸[m∸n]≡n (<⇒≤ i<Dₛᵤₚ) ⟩
    i                     ∎)
    where

    1≤Dₛᵤₚ∸i : 1 ≤ℕ Dₛᵤₚ ∸ i
    1≤Dₛᵤₚ∸i = subst (1 ≤ℕ_) (sym (+-∸-assoc 1 i<Dₛᵤₚ)) (s≤s z≤n)

    Dₛᵤₚ∸i≤hₘₐₓ : Dₛᵤₚ ∸ i ≤ℕ hₘₐₓ
    Dₛᵤₚ∸i≤hₘₐₓ = n∸m≤n i-1 hₘₐₓ
     
    x : Route
    x = h⁻¹ 1≤Dₛᵤₚ∸i Dₛᵤₚ∸i≤hₘₐₓ

    hZ[x]ₛₜ≡Dₛᵤₚ∸i : h (Z[ x ] s t) ≡ Dₛᵤₚ ∸ i
    hZ[x]ₛₜ≡Dₛᵤₚ∸i = trans (cong h (Z[x]ₛₜ≡x x)) h⁻¹-isInverse
    
    hZ[x]ₛₜ<hZₛₜ : h (Z[ x ] s t) <ℕ h (Z s t)
    hZ[x]ₛₜ<hZₛₜ = begin
      suc (h (Z[ x ] s t)) ≡⟨ cong suc hZ[x]ₛₜ≡Dₛᵤₚ∸i ⟩
      suc (Dₛᵤₚ ∸ i)       ≤⟨ m∸n<o⇒m∸o<n (≤⇒pred≤ i<Dₛᵤₚ) Dₛᵤₚ∸hZₛₜ<i ⟩
      h (Z s t)            ∎
      where open ≤-Reasoning

    open ≡-Reasoning

  -- The list of possible values d X Z can take

  abstract
  
    image : List ℕ
    image = zero ∷ between Dₘᵢₙ Dₛᵤₚ

    image<Dₛᵤₚ : All (_<ℕ Dₛᵤₚ) image
    image<Dₛᵤₚ = (s≤s z≤n) ∷ betweenₛₑ<e Dₘᵢₙ Dₛᵤₚ
    
    image! : Unique ℕₛ image
    image! = mapₐ Dₘᵢₙ≤x⇒0≢x (s≤betweenₛₑ Dₘᵢₙ Dₛᵤₚ) ∷ between!⁺ Dₘᵢₙ Dₛᵤₚ

    image-complete : ∀ X → D X Z ∈ image
    image-complete X with X ≟ₘ Z
    ... | yes X≈Z = here (X≈Y⇒D≡0 X≈Z)
    ... | no  X≉Z = there (∈-between⁺ (Dₘᵢₙ≤dXZ X≉Z) (D<Dₛᵤₚ X Z))

    image-sound : ∀ {i} → i ∈ image → ∃ λ X → D X Z ≡ i 
    image-sound {_} (here  refl)  = Z , X≈Y⇒D≡0 ≈ₘ-refl
    image-sound {i} (there i∈btwn) with Z s t ≟ 0# | ∈-between⁻ Dₘᵢₙ Dₛᵤₚ i∈btwn
    ... | yes Zₛₜ≈0# | 2≤i         , i<Dₛᵤₚ = test (begin
      suc (Dₛᵤₚ ∸ h (Z s t)) ≡⟨ cong (λ v → suc (Dₛᵤₚ ∸ v)) (h-resp-≈ Zₛₜ≈0#) ⟩
      suc (Dₛᵤₚ ∸ h 0#)      ≡⟨ cong (λ v → suc (Dₛᵤₚ ∸ v)) (sym hₘₐₓ≡h0) ⟩
      suc (Dₛᵤₚ ∸ hₘₐₓ)      ≡⟨ cong suc (+-∸-assoc 1 {hₘₐₓ} ≤ℕ-refl) ⟩
      2 + (hₘₐₓ ∸ hₘₐₓ)      ≡⟨ cong (2 +_) (n∸n≡0 hₘₐₓ) ⟩
      2                       ≤⟨ 2≤i ⟩
      i ∎) i<Dₛᵤₚ
      where open ≤-Reasoning
    ... | no  Zₛₜ≉0# | Dₛᵤₚ∸hZₛₜ≤i , i<Dₛᵤₚ with Dₛᵤₚ ∸ h (Z s t) ≟ℕ i 
    ...  | yes refl         = ∃X⇒Dₛᵤₚ∸hZₛₜ Zₛₜ≉0# 
    ...  | no  Dₛᵤₚ∸hZₛₜ≢i = test (≤+≢⇒< Dₛᵤₚ∸hZₛₜ≤i Dₛᵤₚ∸hZₛₜ≢i) i<Dₛᵤₚ

    image-sorted : Sorted image
    image-sorted = All-universal (λ _ → z≤n) _ ∷ ↗-between Dₘᵢₙ Dₛᵤₚ
  

{-
  ultrametricConditions : UltrametricConditions σ∥
  ultrametricConditions = record
    { d                 = d
    ; d-isUltrametric   = {!d-isUltrametric!}
    ; d-cong            = d-cong₂
    ; σ-strContr-d      = σ-strictlyContracting
    ; m*                = Z
    ; m*-fixed          = Z-fixed
    ; m*-image          = image
    ; m*-image!         = image!
    ; m*-image-complete = image-complete
    ; m*-image-sound    = image-sound
    }
-}
