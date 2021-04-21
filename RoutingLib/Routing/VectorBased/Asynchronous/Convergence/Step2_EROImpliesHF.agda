open import Data.List
open import Data.List.Properties using (length-filter; filter-notAll)
open import Data.Nat hiding (_≟_; _⊔_)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties as Fin hiding (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.List.Membership.Setoid.Properties
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Binary.Sublist.Setoid.Properties
open import Function using (_∘_; _∘₂_; flip)
open import Level using (_⊔_)
open import Relation.Unary using () renaming (_⊆_ to _⇒_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)

open import RoutingLib.Data.Fin.Properties
open import RoutingLib.Relation.Nullary.Finite.List.Setoid
open import RoutingLib.Function.Reasoning

open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (finite : IsFinite algebra)
  {n} (A : AdjacencyMatrix algebra n)
  {ℓ₂} (extRespOrder : ExtensionRespectingOrder algebra A ℓ₂)
  where

open RawRoutingAlgebra algebra
open import RoutingLib.Routing.Basics.Assignment algebra n as Assignment
  hiding (finite)

open ExtensionRespectingOrder extRespOrder

open import Data.List.Membership.Setoid 𝔸ₛ
open import Data.List.Relation.Binary.Equality.Setoid 𝔸ₛ
  using (_≋_; ≋-refl; ≋-length)
open import Data.List.Relation.Binary.Sublist.Setoid 𝔸ₛ

open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid 𝔸ₛ
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties
import RoutingLib.Data.List.Relation.Binary.Equality.Setoid 𝔸ₛ as Eq

------------------------------------------------------------------------
-- Enumerations

-- As the algebra is finite, we can enumerate the list of all possible
-- assignments

𝔸ₛ-finite : Finite 𝔸ₛ
𝔸ₛ-finite = Assignment.finite finite

open Finite 𝔸ₛ-finite
  renaming
  ( xs to assignments
  ; complete to ∈-assignments
  )

------------------------------------------------------------------------
-- Upwards closed subsets of routes

↑_ : Assignment → List Assignment
↑ x = filter (x <ᵣ?_) assignments

↑-cong : ∀ {x y} → x ≈ₐ y → ↑ x ≋ ↑ y
↑-cong {x} {y} x≈y = Eq.filter⁺ (x <ᵣ?_) (y <ᵣ?_)
  (<ᵣ-resp₂-≈ₐ x≈y)
  (<ᵣ-resp₂-≈ₐ (≈ₐ-sym x≈y) ∘ ≈ₐ-sym)
  (≋-refl {x = assignments})

------------------------------------------------------------------------
-- Height function

h : Assignment → ℕ
h x = suc (length (↑ x))

H : ℕ
H = length assignments

1≤h : ∀ x → 1 ≤ h x
1≤h x = s≤s z≤n

h≤h[0] : ∀ i x → h (i , x) ≤ h (i , 0#)
h≤h[0] i x = begin⟨ (λ {y} → <ᵣ-min {ix} {y}) ⟩
  ∴ (ix <ᵣ_) ⇒ (i0 <ᵣ_) $⟨ (λ v → filter⁺ 𝔸ₛ (ix <ᵣ?_) (i0 <ᵣ?_) (v ∘₂ <ᵣ-respʳ-≈ₐ) (⊆-refl {assignments})) ⟩
  ∴ ↑ ix     ⊆ ↑ i0     $⟨ s≤s ∘ length-mono-≤ 𝔸ₛ ⟩
  ∴ h ix     ≤ h i0     ∎
  where ix = (i , x); i0 = (i , 0#)
  
h-resp-↝ : ∀ {x y} → x ↝[ A ] y → h y < h x
h-resp-↝ {x} {y} x↝y = begin⟨ filter-⊂ 𝔸ₛ _ <ᵣ-respʳ-≈ₐ _ <ᵣ-respʳ-≈ₐ (↝∧<ᵣ⇒<ᵣ x↝y) (∈-assignments y) (↝⇒<ᵣ x↝y) (<ᵣ-irrefl {y} ≈ₐ-refl) ⟩
  ∴ ↑ y ⊂ ↑ x             $⟨ s≤s ∘ length-mono-< 𝔸ₛ ⟩
  ∴ h y < h x             ∎

h-resp-≤ : ∀ {x y} → x <ₐₚ y → h y ≤ h x
h-resp-≤ {x} {y} = begin⟨_⟩
  ∴ x <ₐₚ y    $⟨ (λ v → filter⁺ 𝔸ₛ (y <ᵣ?_) (x <ᵣ?_) (<₊∧<ᵣ⇒<ᵣ v ∘₂ <ᵣ-respʳ-≈ₐ) (⊆-refl {assignments})) ⟩
  ∴ ↑ y ⊆ ↑ x  $⟨ s≤s ∘ length-mono-≤ 𝔸ₛ ⟩
  ∴ h y ≤ h x  ∎

h-cong : ∀ {x y} → x ≈ₐ y → h x ≡ h y
h-cong {x} {y} x≈y = begin⟨ x≈y ⟩
  ∴   x ≈ₐ  y  $⟨ ↑-cong ⟩
  ∴ ↑ x ≋ ↑ y  $⟨ cong suc ∘ ≋-length ⟩
  ∴ h x ≡ h y  ∎

heightFunction : HeightFunction algebra A
heightFunction = record
  { h        = h
  ; h-cong   = h-cong
  ; 1≤h      = 1≤h
  ; h≤h[0]   = h≤h[0]
  ; h-resp-≤ = h-resp-≤
  ; h-resp-↝ = h-resp-↝
  }
