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
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions using (SufficientConditions)
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

module RoutingLib.Routing.BellmanFord.GeneralConvergence.Step4_AsynchronousConditions
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1))
  (sc : SufficientConditions 𝓡𝓐)
  where
  
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step1_HeightFunction 𝓡𝓟 sc using (h; hₘₐₓ; h≤hₘₐₓ; h⁻¹; h⁻¹-isInverse; h-resp-≈; h-resp-<; hₘₐₓ≡h0)
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_Ultrametric 𝓡𝓟 sc using (d; dₑ; d-cong₂; dₛᵤₚ; d<dₛᵤₚ; d≡dₛᵤₚ∸Xᵢⱼ; x≈y⇒dₑ≡0; d≢1; X≈Y⇒d≡0; x≉y⇒0<dₑ; h≤dₛᵤₚ; d≡dₑ; dₛᵤₚ∸hYᵢⱼ≤d; dₑ≤d; d≡dₛᵤₚ∸Yᵢⱼ; d-isUltrametric; d≡0⇒X≈Y; d-findWorstDisagreement; x≉y⇒dₑ≡dₕ)
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step3_StrictlyContracting 𝓡𝓟 sc using (σ-strictlyContracting; σ-strictlyContractingOnOrbits)
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions.Properties 𝓡𝓟 sc using (σXᵢᵢ≈σYᵢᵢ; σXᵢⱼ≤Aᵢₖ▷Xₖⱼ; σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ)

  open import RoutingLib.Routing.BellmanFord 𝓡𝓟
  open import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 using (Iᵢⱼ≡0#)

  open RoutingProblem 𝓡𝓟
  open SufficientConditions sc

  
  open import RoutingLib.Function.Distance.Properties using (x*; x*-fixed)

  private

    n : ℕ
    n = suc n-1

  -- Z is the unique fixed point of σ
  
  Z : RMatrix
  Z = x* ℝ𝕄ₛ _≟ₘ_ d σ-strictlyContractingOnOrbits I
  
  Z-fixed : σ Z ≈ₘ Z
  Z-fixed = x*-fixed ℝ𝕄ₛ _≟ₘ_ d σ-strictlyContractingOnOrbits I

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


  -- As Zₛₜ is the maximial element we can define the minimal distance
  -- any matrix can be from Z (excluding Z itself)

  dₘᵢₙ : ℕ
  dₘᵢₙ with Z s t ≟ 0#
  ... | yes _ = 2
  ... | no  _ = dₛᵤₚ ∸ h (Z s t)
  
  dₘᵢₙ≤dXZ : ∀ {X} → X ≉ₘ Z → dₘᵢₙ ≤ℕ d X Z
  dₘᵢₙ≤dXZ {X} X≉Z with Z s t ≟ 0# | ≉ₘ-witness X≉Z
  ... | no  _      | i , j , Xᵢⱼ≉Zᵢⱼ = ≤ℕ-trans (∸-mono ≤ℕ-refl (hZᵢⱼ≤hZₛₜ i j)) (dₛᵤₚ∸hYᵢⱼ≤d Xᵢⱼ≉Zᵢⱼ)
  ... | yes Zₛₜ≈0# | _              with d X Z | inspect (d X) Z
  ...   | zero        | [ dXZ≡0 ] = contradiction (d≡0⇒X≈Y dXZ≡0) X≉Z
  ...   | suc zero    | [ dXZ≡1 ] = contradiction dXZ≡1 (d≢1 X Z)
  ...   | suc (suc n) | _         = s≤s (s≤s z≤n)
  
  dₘᵢₙ≤x⇒0≢x : {x : ℕ} → dₘᵢₙ ≤ℕ x → 0 ≢ x
  dₘᵢₙ≤x⇒0≢x {suc x} dₘᵢₙ≤x ()
  dₘᵢₙ≤x⇒0≢x {zero}  dₘᵢₙ≤x with Z s t ≟ 0#
  ... | yes _ = contradiction dₘᵢₙ≤x λ()
  ... | no  _ = contradiction (subst (_≤ℕ 0) (+-∸-assoc 1 h≤hₘₐₓ) dₘᵢₙ≤x) λ()


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

  dₑZᵢⱼ≤dₑZₛₜ : ∀ {x} → ∀ i j → dₑ (Z[ x ] i j) (Z i j) ≤ℕ dₑ (Z[ x ] s t) (Z s t)
  dₑZᵢⱼ≤dₑZₛₜ i j with i ≟𝔽 s | j ≟𝔽 t
  ... | no  _    | _        = subst (_≤ℕ _) (sym (x≈y⇒dₑ≡0 ≈-refl)) z≤n
  ... | yes _    | no _     = subst (_≤ℕ _) (sym (x≈y⇒dₑ≡0 ≈-refl)) z≤n
  ... | yes refl | yes refl with s ≟𝔽 s | t ≟𝔽 t
  ...   | no  s≢s   | _       = contradiction refl s≢s
  ...   | yes _     | no  t≢t = contradiction refl t≢t
  ...   | yes _     | yes _   = ≤ℕ-refl

  Zₛₜ<Z[0]ₛₜ : Z s t ≉ 0# → Z s t < Z[ 0# ] s t
  Zₛₜ<Z[0]ₛₜ Zₛₜ≉0# with s ≟𝔽 s | t ≟𝔽 t
  ... | yes _     | yes _   = 0#-idₗ-⊕ (Z s t) , Zₛₜ≉0#
  ... | no  s≢s   | _       = contradiction refl s≢s
  ... | yes _     | no  t≢t = contradiction refl t≢t

  ∃X⇒dₛᵤₚ∸hZₛₜ : Z s t ≉ 0# →  ∃ λ X → d X Z ≡ dₛᵤₚ ∸ h (Z s t)
  ∃X⇒dₛᵤₚ∸hZₛₜ Zₛₜ≉0# = Z[ 0# ] , d≡dₛᵤₚ∸Yᵢⱼ dₑZᵢⱼ≤dₑZₛₜ (h-resp-< (Zₛₜ<Z[0]ₛₜ Zₛₜ≉0#))
  
  test : ∀ {i} → dₛᵤₚ ∸ h (Z s t) <ℕ i → i <ℕ dₛᵤₚ → ∃ λ X → d X Z ≡ i 
  test {i} dₛᵤₚ∸hZₛₜ<i i<dₛᵤₚ with m<n⇒n≡1+o dₛᵤₚ∸hZₛₜ<i
  ... | (i-1 , refl) = Z[ x ] , (begin
    d Z[ x ] Z            ≡⟨ d≡dₛᵤₚ∸Xᵢⱼ dₑZᵢⱼ≤dₑZₛₜ hZ[x]ₛₜ<hZₛₜ ⟩
    dₛᵤₚ ∸ h (Z[ x ] s t) ≡⟨ cong (dₛᵤₚ ∸_) hZ[x]ₛₜ≡dₛᵤₚ∸i ⟩
    dₛᵤₚ ∸ (dₛᵤₚ ∸ i)     ≡⟨ m∸[m∸n]≡n (<⇒≤ i<dₛᵤₚ) ⟩
    i                     ∎)
    where

    1≤dₛᵤₚ∸i : 1 ≤ℕ dₛᵤₚ ∸ i
    1≤dₛᵤₚ∸i = subst (1 ≤ℕ_) (sym (+-∸-assoc 1 i<dₛᵤₚ)) (s≤s z≤n)

    dₛᵤₚ∸i≤hₘₐₓ : dₛᵤₚ ∸ i ≤ℕ hₘₐₓ
    dₛᵤₚ∸i≤hₘₐₓ = n∸m≤n i-1 hₘₐₓ
     
    x : Route
    x = h⁻¹ 1≤dₛᵤₚ∸i dₛᵤₚ∸i≤hₘₐₓ

    hZ[x]ₛₜ≡dₛᵤₚ∸i : h (Z[ x ] s t) ≡ dₛᵤₚ ∸ i
    hZ[x]ₛₜ≡dₛᵤₚ∸i = trans (cong h (Z[x]ₛₜ≡x x)) h⁻¹-isInverse
    
    hZ[x]ₛₜ<hZₛₜ : h (Z[ x ] s t) <ℕ h (Z s t)
    hZ[x]ₛₜ<hZₛₜ = begin
      suc (h (Z[ x ] s t)) ≡⟨ cong suc hZ[x]ₛₜ≡dₛᵤₚ∸i ⟩
      suc (dₛᵤₚ ∸ i)       ≤⟨ m∸n<o⇒m∸o<n (≤⇒pred≤ i<dₛᵤₚ) dₛᵤₚ∸hZₛₜ<i ⟩
      h (Z s t)            ∎
      where open ≤-Reasoning

    open ≡-Reasoning

  -- The list of possible values d X Z can take

  abstract
  
    image : List ℕ
    image = zero ∷ between dₘᵢₙ dₛᵤₚ

    image<dₛᵤₚ : All (_<ℕ dₛᵤₚ) image
    image<dₛᵤₚ = (s≤s z≤n) ∷ betweenₛₑ<e dₘᵢₙ dₛᵤₚ
    
    image! : Unique ℕₛ image
    image! = mapₐ dₘᵢₙ≤x⇒0≢x (s≤betweenₛₑ dₘᵢₙ dₛᵤₚ) ∷ between!⁺ dₘᵢₙ dₛᵤₚ

    image-complete : ∀ X → d X Z ∈ image
    image-complete X with X ≟ₘ Z
    ... | yes X≈Z = here (X≈Y⇒d≡0 X≈Z)
    ... | no  X≉Z = there (∈-between⁺ (dₘᵢₙ≤dXZ X≉Z) (d<dₛᵤₚ X Z))

    image-sound : ∀ {i} → i ∈ image → ∃ λ X → d X Z ≡ i 
    image-sound {_} (here  refl)  = Z , X≈Y⇒d≡0 ≈ₘ-refl
    image-sound {i} (there i∈btwn) with Z s t ≟ 0# | ∈-between⁻ dₘᵢₙ dₛᵤₚ i∈btwn
    ... | yes Zₛₜ≈0# | 2≤i         , i<dₛᵤₚ = test (begin
      suc (dₛᵤₚ ∸ h (Z s t)) ≡⟨ cong (λ v → suc (dₛᵤₚ ∸ v)) (h-resp-≈ Zₛₜ≈0#) ⟩
      suc (dₛᵤₚ ∸ h 0#)      ≡⟨ cong (λ v → suc (dₛᵤₚ ∸ v)) (sym hₘₐₓ≡h0) ⟩
      suc (dₛᵤₚ ∸ hₘₐₓ)      ≡⟨ cong suc (+-∸-assoc 1 {hₘₐₓ} ≤ℕ-refl) ⟩
      2 + (hₘₐₓ ∸ hₘₐₓ)      ≡⟨ cong (2 +_) (n∸n≡0 hₘₐₓ) ⟩
      2                       ≤⟨ 2≤i ⟩
      i ∎) i<dₛᵤₚ
      where open ≤-Reasoning
    ... | no  Zₛₜ≉0# | dₛᵤₚ∸hZₛₜ≤i , i<dₛᵤₚ with dₛᵤₚ ∸ h (Z s t) ≟ℕ i 
    ...  | yes refl         = ∃X⇒dₛᵤₚ∸hZₛₜ Zₛₜ≉0# 
    ...  | no  dₛᵤₚ∸hZₛₜ≢i = test (≤+≢⇒< dₛᵤₚ∸hZₛₜ≤i dₛᵤₚ∸hZₛₜ≢i) i<dₛᵤₚ

    image-sorted : Sorted image
    image-sorted = All-universal (λ _ → z≤n) _ ∷ ↗-between dₘᵢₙ dₛᵤₚ
  

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
