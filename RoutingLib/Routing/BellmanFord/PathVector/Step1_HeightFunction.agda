open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; ≤-pred)
open import Data.Nat.Properties using (≤-refl; <-irrefl)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph.SimplePath using (SimplePath; length)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction as Step1ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step1_HeightFunction
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒
  open import RoutingLib.Routing.BellmanFord.DistanceVector.Step1_HeightFunction 𝓡𝓟ᶜ 𝓢𝓒 using () renaming (hₘₐₓ to Hᶜ)
  
  ------------------------------------------------------------------------------
  -- Inconsistent length
  ------------------------------------------------------------------------------
  -- The size of inconsistent routes where consistent routes are viewed as
  -- having the maximum size `n-1`
  
  hⁱ : Route → ℕ
  hⁱ r with 𝑪? r
  ... | yes _ = n-1
  ... | no  _ = size r
  
  Hⁱ : ℕ
  Hⁱ = n
  
  postulate hⁱ[rᶜ]≡n-1 : ∀ {r} → 𝑪 r → hⁱ r ≡ n-1
  {-
  ⟨rᶜ⟩≡Hᶜ+n {r} rᶜ with 𝑪? r
  ... | yes _  = refl
  ... | no  rⁱ = contradiction rᶜ rⁱ
  -}
  
  postulate hⁱ[rⁱ]≡|r| : ∀ {r} → 𝑰 r → hⁱ r ≡ size r
  {-
  ⟨rⁱ⟩≡Hᶜ+|r| {r} rⁱ with 𝑪? r
  ... | yes rᶜ = contradiction rᶜ rⁱ
  ... | no  _  = refl
  -}
  
  hⁱ-cong : ∀ {r s} → r ≈ s → hⁱ r ≡ hⁱ s
  hⁱ-cong {r} {s} r≈s with 𝑪? r | 𝑪? s
  ... | yes _  | yes _  = refl
  ... | no  rⁱ | yes sᶜ = contradiction (𝑪-cong (≈-sym r≈s) sᶜ) rⁱ
  ... | yes rᶜ | no  sⁱ = contradiction (𝑪-cong r≈s rᶜ) sⁱ
  ... | no  _  | no  _  = size-cong r≈s

  postulate hⁱ≤n-1 : ∀ r → hⁱ r ≤ n-1
  {-
  ⟨r⟩≤Hᶜ+n r with 𝑪? r
  ... | yes _ = ≤-refl
  ... | no  _ = {!subst₂ _≤_ ? ?!} --≤-pred (size<n r)
  -}
  
  postulate hⁱ[r]<n-1⇒rⁱ : ∀ {r} → hⁱ r < n-1 → 𝑰 r
  {-
  ⟨r⟩<n-1⇒rⁱ {r} |r|<n-1 with 𝑪? r
  ... | yes _  = contradiction |r|<n-1 (<-irrefl refl)
  ... | no  rⁱ = rⁱ
  -}
  
  postulate hⁱ[rⁱ]≡|p| : ∀ {r} → 𝑰 r → ∃ λ (p : SimplePath n) → hⁱ r ≡ length p
  {-
  ⟨rⁱ⟩≡Hᶜ+|p| {r} rⁱ with 𝑪? r
  ... | yes rᶜ = contradiction rᶜ rⁱ  
  ... | no  _  with r ≟ 0#
  ...   | yes r≈0 = contradiction (𝒄-null r≈0) rⁱ
  ...   | no  r≉0 = path r≉0 , refl
  -}

  postulate hⁱ[r]≢0 : ∀ r → hⁱ r ≢ 0

