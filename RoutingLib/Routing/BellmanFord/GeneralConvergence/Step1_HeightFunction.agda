open import Data.Nat using (ℕ; suc; z≤n; s≤s; ≤-pred) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (≰⇒>; <⇒≱; <⇒≤; suc-injective) renaming (≤-reflexive to ≤ℕ-reflexive)
open import Data.List using (List; length)
open import Data.List.All.Properties using (All-universal)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst) renaming (refl to ≡-refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions using (SufficientConditions)
open import RoutingLib.Data.List using (index)
open import RoutingLib.Data.List.Uniqueness using (Unique)

module RoutingLib.Routing.BellmanFord.GeneralConvergence.Step1_HeightFunction 
  {a b ℓ n}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) 
  (sc : SufficientConditions 𝓡𝓐)
  where
  
  open RoutingProblem 𝓡𝓟
  open SufficientConditions sc
  open import RoutingLib.Data.List.Uniset DS using (Enumeration)
  open import Data.List.Any.Membership S using (_∈_)
  open import RoutingLib.Data.List.Any.Membership S using (indexOf)
  open import RoutingLib.Data.List.Any.Membership.Properties using (indexOf-cong; indexOf-revCong; indexOf-index)

  open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted; sort; sort-↗; _↗_; sort-Sorted)
  open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-unique; ↗-∈ˡ; ↗-indexOf-mono-<; ↗-indexOf-revMono-≤; ↗-indexOf-⊤)

  open Enumeration routes-enumerable renaming (X to R-uniset; isEnumeration to R-isEnumeration)

  abstract
  
    -- We have a unique complete list of routes

    routes : List Route
    routes = proj₁ R-uniset

    routes! : Unique S routes
    routes! = proj₂ R-uniset

    ∈-routes : ∀ x → x ∈ routes
    ∈-routes = R-isEnumeration


    -- We can then sort this, preserving the completeness and uniqueness
  
    ↗routes : List Route
    ↗routes = sort routes
    
    ↗routes! : Unique S ↗routes
    ↗routes! = ↗-unique routes! (sort-↗ routes)

    ∈-↗routes : ∀ x → x ∈ ↗routes
    ∈-↗routes x = ↗-∈ˡ (∈-routes x) (sort-↗ routes)

    ↗-↗routes : Sorted ↗routes
    ↗-↗routes = sort-Sorted routes


    -- The height of an element x is h(x) = |{y | y ≤ x}|

    h : Route → ℕ
    h x = suc (indexOf (∈-↗routes x))

    h-resp-≈ : ∀ {u v} → u ≈ v → h u ≡ h v
    h-resp-≈ u≈v = cong suc (indexOf-cong S u≈v _ _ ↗routes!)

    ≈-resp-h : ∀ {u v} → h u ≡ h v → u ≈ v
    ≈-resp-h hᵤ≡hᵥ = indexOf-revCong S _ _ (suc-injective hᵤ≡hᵥ)

    h-resp-< : ∀ {u v} → u ≤ v × ¬ (u ≈ v) → h u <ℕ h v
    h-resp-< u<v = s≤s (↗-indexOf-mono-< ↗-↗routes _ _ u<v)

    h-resp-≤ : h Preserves _≤_ ⟶ _≤ℕ_
    h-resp-≤ {u} {v} u≤v with u ≟ v
    ... | yes u≈v = ≤ℕ-reflexive (h-resp-≈ u≈v)
    ... | no  u≉v = <⇒≤ (h-resp-< (u≤v , u≉v))

    ≤-resp-h : ∀ {u v} → h u ≤ℕ h v → u ≤ v
    ≤-resp-h h[u]≤h[v] = ↗-indexOf-revMono-≤ ↗-↗routes _ _ (≤-pred h[u]≤h[v])
  

    -- We have a maximal element

    hₘₐₓ : ℕ
    hₘₐₓ = h 0#

    1≤h : ∀ x → 1 ≤ℕ h x
    1≤h x = s≤s z≤n

    h≤hₘₐₓ : ∀ {x} → h x ≤ℕ hₘₐₓ
    h≤hₘₐₓ = h-resp-≤ (0#-idₗ-⊕ _)

    hₘₐₓ≡|routes| : hₘₐₓ ≡ length ↗routes
    hₘₐₓ≡|routes| = ↗-indexOf-⊤ ↗-↗routes ↗routes! _ (All-universal 0#-idₗ-⊕ ↗routes)

    hₘₐₓ≡h0 : hₘₐₓ ≡ h 0#
    hₘₐₓ≡h0 = ≡-refl

    -- Furthermore for any valid height, we can retrieve the route with that height

    h⁻¹ : ∀ {i} → 1 ≤ℕ i → i ≤ℕ hₘₐₓ → Route
    h⁻¹ {suc i} (s≤s z≤n) i≤hₘₐₓ rewrite hₘₐₓ≡|routes| = index ↗routes i≤hₘₐₓ

    h⁻¹-isInverse : ∀ {i} {1≤i : 1 ≤ℕ i} {i≤hₘₐₓ} → h (h⁻¹ 1≤i i≤hₘₐₓ) ≡ i
    h⁻¹-isInverse {_} {s≤s z≤n} {i≤hₘₐₓ} rewrite hₘₐₓ≡|routes| = cong suc (indexOf-index S ↗routes! i≤hₘₐₓ (∈-↗routes _))
