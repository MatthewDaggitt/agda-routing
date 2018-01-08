open import Data.Nat using (ℕ; suc; _+_; _∸_; _⊓_; _≤_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m≤m+n; ≤-decTotalOrder)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; map; _++_; gfilter)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.All using (All; lookup)
open import Data.List.All.Properties using (All-map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (subst; cong; _≡_; module ≡-Reasoning)
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Algebra.FunctionProperties.Consequences using (idˡ-subst; idˡ+zeˡ⇒singleton)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; length; _∈𝔾_; _∉𝔾_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (ℙₛ; p≈q⇒|p|≡|q|; _∈𝔾?_; _∉𝔾?_; ∉𝔾-resp-≈)
open import RoutingLib.Data.Graph.SimplePath.Enumeration
open import RoutingLib.Data.List using (dfilter)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique; deduplicate!⁺; ++!⁺; map!⁺)
open import RoutingLib.Data.List.Any.Membership.Propositional using (deduplicate; ∈-++⁺ʳ; ∈-++⁺ˡ; ∈-++⁻; ∈-deduplicate⁺; ∈-deduplicate⁻)
open import RoutingLib.Data.List.Any.Membership.Properties using (∈-map⁺; ∈-map⁻; ∈-dfilter⁻; ∈-dfilter⁺)
open import RoutingLib.Data.List.All.Properties using (AllPairs-deduplicate⁺; deduplicate⁺; All-map⁺₂; AllPairs-map⁺₂; AllPairs-++⁺)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
import RoutingLib.Data.Matrix as Matrix
open import RoutingLib.Data.Matrix.Properties using (min⁺-constant)
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ℕᵈˢ; ≤⇒≯)
open import RoutingLib.Data.List.Disjoint ℕₛ using (_#_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Asynchronous.Theorems using (UltrametricConditions)
import RoutingLib.Routing.AlgebraicPaths.Inconsistent as InconsistentPaths
import RoutingLib.Routing.AlgebraicPaths.Consistent as ConsistentPaths
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude

import RoutingLib.Routing.BellmanFord.PathVector.Step1_Ultrametric as Step1
import RoutingLib.Routing.BellmanFord.PathVector.Step2_StrictlyContracting as Step2

import RoutingLib.Routing.BellmanFord.DistanceConvergence.Step2_Ultrametric as ConsistentUltrametric
import RoutingLib.Routing.BellmanFord.DistanceConvergence.Step4_AsynchronousConditions as ConsistentAsyncConditions

module RoutingLib.Routing.BellmanFord.PathVector.Step4_AsynchronousConditions
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒

  open Step1 𝓟𝓢𝓒
  open Step2 𝓟𝓢𝓒 using (σ-strContr-dⁱ)

  open ConsistentUltrametric 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( d              to dᶜ
    ; d-cong₂        to dᶜ-cong
    ; dₛᵤₚ           to dᶜₛᵤₚ
    ; X≈Y⇒d≡0        to X≈Y⇒dᶜ≡0)
  open ConsistentAsyncConditions 𝓡𝓟ᶜ 𝓢𝓒 using () renaming
    ( image          to imageᶜ
    ; image<dₛᵤₚ     to imageᶜ<dᶜₛᵤₚ
    ; image!         to imageᶜ!
    ; image-complete to imageᶜ-complete'
    ; image-sound    to imageᶜ-sound'
    ; image-sorted   to imageᶜ-sorted
    ; Z              to cZ
    ; Z-fixed        to cZ-fixed
    )
  
  ------------------------------------------------------------------------------
  -- Fixed point
  ------------------------------------------------------------------------------
  -- As applications of σ perserves consistency then Z, the fixed point for σᶜ,
  -- is also the fixed point for σⁱ
  
  Z : RMatrix
  Z i j = proj₁ (cZ i j)

  Zᶜ : 𝑪ₘ Z
  Zᶜ i j = proj₂ (cZ i j)
  
  postulate Z-fixed : σ Z ≈ₘ Z
  {-
  Z-fixed = proj₁ (begin
    fromIₘ (σⁱ-pres-𝑪ₘ Zᶜ) ≈⟨ σ-fromIₘ-commute Zᶜ _ ⟩
    σᶜ (fromIₘ Zᶜ)          ≈⟨ σᶜ-cong (fromIₘ-toIₘ (toIₘᶜ cZ)) ⟩
    σᶜ (cZ)                 ≈⟨ cZ-fixed ⟩
    cZ                      ≈⟨ ≈ᶜₘ-sym (fromIₘ-toIₘ (toIₘᶜ cZ)) ⟩
    fromIₘ Zᶜ               ∎)
    where
    open RoutingProblem 𝓡𝓟ᶜ renaming (ℝ𝕄ₛ to ℝ𝕄ᶜₛ)
    open import Relation.Binary.EqReasoning ℝ𝕄ᶜₛ

  
  Z≉Xⁱ : ∀ {X} → 𝑰ₘ X → Z ≉ₘ X
  Z≉Xⁱ Xⁱ X≈Z = Xⁱ (𝑪ₘ-cong Zᶜ X≈Z)
  -}
  
  ------------------------------------------------------------------------------
  -- Paths to inconsistent routes
  ------------------------------------------------------------------------------
  -- Given a path we can always create an inconsistent IRoute

  inconsistentIRoute : SimplePath n → Maybe Route
  inconsistentIRoute p with path-inconsistent p
  ...   | yes (r , _) = just r
  ...   | no  _       = nothing 

{-
  inconsistentIRouteⁱ : ∀ p → 𝑰 (inconsistentIRoute p)
  inconsistentIRouteⁱ p pᶜ with p ∈𝔾? G
  ... | no  p∉G = contradiction pᶜ (𝒊-route-∉ 0# p∉G)
  ... | yes p∈G with weight p∈G ≟ 0#
  ...   | yes wₚ≈0 = contradiction pᶜ (𝒊-route-≉ p∈G (λ 1≈wₚ → 0≉1 (sym (trans 1≈wₚ wₚ≈0))))
  ...   | no  wₚ≉0 = contradiction pᶜ (𝒊-route-≉ p∈G (wₚ≉0 ∘ sym)) 

  inconsistentIRoute-size : ∀ p → sizeⁱ (inconsistentIRoute p) ≡ length p
  inconsistentIRoute-size p with p ∈𝔾? G
  ... | no  _   = ≡-refl
  ... | yes p∈G with weight p∈G ≟ 0#
  ...   | yes _ = ≡-refl
  ...   | no  _ = ≡-refl
  
  inconsistentIRoute-sizeⁱ : ∀ p → lengthⁱ (inconsistentIRoute p) ≡ length p
  inconsistentIRoute-sizeⁱ p with 𝑪? (inconsistentIRoute p)
  ... | yes c = contradiction c (inconsistentIRouteⁱ p)
  ... | no  _ = inconsistentIRoute-size p


  ------------------------------------------------------------------------------
  -- Manufacturing a matrix with at a specific distance
  ------------------------------------------------------------------------------
  -- The matrix Z[ p ] is defined such that the distance between Z[ p ] and Z
  -- will always equal `invert (length p)`
  
  Z[_] : SimplePath n → IMatrix
  Z[ p ] i j = inconsistentIRoute p

  Z[p]ⁱ : ∀ p → 𝑰ₘ Z[ p ]
  Z[p]ⁱ p Z[p]ᶜ = contradiction (Z[p]ᶜ fzero fzero) (inconsistentIRouteⁱ p)

  Z[p]≉Z : ∀ p → Z[ p ] ≉ⁱₘ Z
  Z[p]≉Z p = Z≉Xⁱ (Z[p]ⁱ p) ∘ ≈ⁱₘ-sym

  shZ[p]≡|p| : ∀ p → shortest Z[ p ] ≡ length p
  shZ[p]≡|p| p = min⁺-constant {n-1} {n-1} (λ i j → inconsistentIRoute-sizeⁱ p)

  dZ[p]Z≡inv|p| : ∀ p → d Z[ p ] Z ≡ invert (length p)
  dZ[p]Z≡inv|p| p = begin
    d Z[ p ] Z                            ≡⟨ d≡dⁱ (Z[p]≉Z p) (inj₁ (Z[p]ⁱ p)) ⟩
    invert (shortest Z[ p ] ⊓ shortest Z) ≡⟨ cong invert (Yᶜ⇒shX⊓shY≡shX Z[ p ] Zᶜ) ⟩
    invert (shortest Z[ p ])              ≡⟨ cong invert (shZ[p]≡|p| p) ⟩
    invert (length p)                     ∎
    where open ≡-Reasoning


  ------------------------------------------------------------------------------
  -- All inconsistent distances
  ------------------------------------------------------------------------------
  -- A unique list of all the possible distances between Z and inconsistent
  -- states
-}

  imageⁱ : List ℕ
  imageⁱ = deduplicate _≟ℕ_ (gfilter (invert ∘ size) (allPaths n))

{-
  imageⁱ≥dᶜₛᵤₚ : All (dᶜₛᵤₚ ≤_) imageⁱ
  imageⁱ≥dᶜₛᵤₚ = deduplicate⁺ ℕᵈˢ (All-map⁺₂ (λ _ → m≤m+n dᶜₛᵤₚ _) (allPaths n))
  
  ∈-imageⁱ⁺ : ∀ (p : SimplePath n) → invert (length p) ∈ imageⁱ
  ∈-imageⁱ⁺ p = ∈-deduplicate⁺ _≟ℕ_ (∈-map⁺ ℙₛ ℕₛ (cong invert ∘ p≈q⇒|p|≡|q|) (∈-allPaths p))

  ∈-imageⁱ⁻ : ∀ {l} → l ∈ imageⁱ → ∃ λ (p : SimplePath n) → invert (length p) ≡ l
  ∈-imageⁱ⁻ l∈dedup with ∈-deduplicate⁻ _≟ℕ_ l∈dedup
  ... | l∈map with ∈-map⁻ ℙₛ ℕₛ {xs = allPaths n} l∈map
  ...   | p , _ , l≡inv|p| = p , ≡-sym l≡inv|p|
  
  imageⁱ! : Unique imageⁱ
  imageⁱ! = deduplicate!⁺ _≟ℕ_ (map (invert ∘ length) (allPaths n))

  imageⁱ-complete : ∀ {X} → 𝑰ₘ X → d X Z ∈ imageⁱ
  imageⁱ-complete {X} Xⁱ with d≡inv|p| ((Z≉Xⁱ Xⁱ) ∘ ≈ⁱₘ-sym) (inj₁ Xⁱ)
  ... | p , d≡inv|p| = subst (_∈ imageⁱ) (≡-sym d≡inv|p|) (∈-imageⁱ⁺ p)

  imageⁱ-sound : ∀ {i} → i ∈ imageⁱ → ∃ λ X → d X Z ≡ i
  imageⁱ-sound {i} i∈imageⁱ with ∈-imageⁱ⁻ i∈imageⁱ
  ... | p , inv|p|≡i = Z[ p ] , ≡-trans (dZ[p]Z≡inv|p| p) inv|p|≡i

  imageⁱ-sorted : Sorted imageⁱ
  imageⁱ-sorted = AllPairs-deduplicate⁺ ℕᵈˢ (AllPairs-map⁺₂ {!!} (allPaths-sortedByLength n))

  ------------------------------------------------------------------------------
  -- All consistent distances
  ------------------------------------------------------------------------------
  -- A unique list of all the possible distances between Z and consistent states
  
  imageᶜ-complete : ∀ {X} → 𝑪ₘ X → d X Z ∈ imageᶜ
  imageᶜ-complete {X} Xᶜ with X ≟ⁱₘ Z
  ... | yes _ = subst (_∈ imageᶜ) (X≈Y⇒dᶜ≡0 ≈ᶜₘ-refl) (imageᶜ-complete' cZ)
  ... | no  _ with 𝑪ₘ? X | 𝑪ₘ? Z
  ... | no  Xⁱ | _      = contradiction Xᶜ Xⁱ
  ... | _      | no  Zⁱ = contradiction Zᶜ Zⁱ
  ... | yes Xᶜ' | yes Zᶜ = subst (_∈ imageᶜ) (dᶜ-cong ≈ᶜₘ-refl (≈ᶜₘ-sym (fromIₘ-toIₘ Zᶜ))) (imageᶜ-complete' (fromIₘ Xᶜ'))

  imageᶜ-sound : ∀ {i} → i ∈ imageᶜ → ∃ λ X → d X Z ≡ i
  imageᶜ-sound i∈imageᶜ with imageᶜ-sound' i∈imageᶜ
  ... | X , dᶜXZ≡i = toIₘ X , ≡-trans (d≡dᶜ X cZ) dᶜXZ≡i

  imageᶜ#imageⁱ : imageᶜ # imageⁱ
  imageᶜ#imageⁱ (l∈imageᶜ , l∈imageⁱ) =
    contradiction
      (lookup imageᶜ<dᶜₛᵤₚ l∈imageᶜ)
      (≤⇒≯ (lookup imageⁱ≥dᶜₛᵤₚ l∈imageⁱ))


  ------------------------------------------------------------------------------
  -- All distances
  ------------------------------------------------------------------------------
  -- A unique list of all the possible distances between Z and other states

  image : List ℕ
  image =  imageᶜ ++ imageⁱ 

  image! : Unique image
  image! = ++!⁺ imageᶜ! imageⁱ! imageᶜ#imageⁱ

  image-complete : ∀ X → d X Z ∈ image
  image-complete X with 𝑪ₘ? X
  ... | yes Xᶜ = ∈-++⁺ˡ (imageᶜ-complete Xᶜ)
  ... | no  Xⁱ = ∈-++⁺ʳ imageᶜ (imageⁱ-complete Xⁱ)
  
  image-sound : ∀ {i} → i ∈ image → ∃ λ X → d X Z ≡ i
  image-sound i∈image with ∈-++⁻ imageᶜ i∈image
  ... | inj₁ i∈imageᶜ = imageᶜ-sound i∈imageᶜ
  ... | inj₂ i∈imageⁱ = imageⁱ-sound i∈imageⁱ

  image-sorted : Sorted image
  image-sorted = AllPairs-++⁺ {!!} {!!} {!!}

{-
  ultrametricConditions : UltrametricConditions σ∥
  ultrametricConditions = record
    { d                 = dⁱ
    ; d-isUltrametric   = {!!}
    ; d-cong            = dⁱ-cong₂
    ; σ-strContr-d      = σ-strContrOver-dⁱ
    ; m*                = Z
    ; m*-fixed          = Z-fixed
    ; m*-image          = image
    ; m*-image!         = image!
    ; m*-image-complete = image-complete
    ; m*-image-sound    = image-sound
    }
-}
-}
