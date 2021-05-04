open import Data.List
open import Data.List.Properties using (length-filter; filter-notAll)
open import Data.Nat hiding (_≟_; _⊔_)
open import Data.Nat.Properties using (<⇒≤)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties as Fin hiding (_≟_)
open import Data.Product using (∃; _×_; _,_)
open import Data.List.Membership.Setoid.Properties
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Binary.Sublist.Setoid.Properties
open import Function using (_∘_; _∘₂_; flip)
open import Level using (_⊔_)
open import Relation.Unary using () renaming (_⊆_ to _⇒_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)
open import Relation.Binary.Definitions

open import RoutingLib.Data.Fin.Properties
open import RoutingLib.Relation.Nullary.Finite.List.Setoid
open import RoutingLib.Function.Reasoning

open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF
  {ℓ₁ ℓ₂ ℓ₃} (algebra : RawRoutingAlgebra ℓ₁ ℓ₂ ℓ₃)
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

private
  variable
    a b : Assignment
    
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
↑ a = filter (a <ᵣ?_) assignments

↑-cong : a ≈ₐ b → ↑ a ≋ ↑ b
↑-cong {a} {b} a≈b = Eq.filter⁺ (a <ᵣ?_) (b <ᵣ?_)
  (<ᵣ-resp₂-≈ₐ a≈b)
  (<ᵣ-resp₂-≈ₐ (≈ₐ-sym a≈b) ∘ ≈ₐ-sym)
  (≋-refl {x = assignments})

↑-resp-<ᵣ : a <ᵣ b → ↑ b ⊂ ↑ a
↑-resp-<ᵣ {a} {b} a<b = filter-⊂ 𝔸ₛ
  _ <ᵣ-respʳ-≈ₐ _ <ᵣ-respʳ-≈ₐ
  (<ᵣ-trans a<b)
  (∈-assignments b)
  (<ᵣ-irrefl ≈ₐ-refl)
  a<b

------------------------------------------------------------------------
-- Height function

h : Assignment → ℕ
h a = length (↑ a) 

h-bounded : ∃ λ H → ∀ a → h a ≤ H
h-bounded = length assignments , λ a → length-filter (a <ᵣ?_) assignments

h-resp-↝ : a ↝[ A ] b → h b < h a
h-resp-↝ {a} {b} a↝b = begin⟨ a↝b ⟩
  ∴ a ↝[ A ] b  $⟨ ↝⇒<ᵣ ⟩
  ∴ a   <ᵣ   b  $⟨ ↑-resp-<ᵣ ⟩ 
  ∴ ↑ b ⊂ ↑  a  $⟨ length-mono-< 𝔸ₛ ⟩
  ∴ h b < h  a  ∎

h-resp-< : a <ₐₚ b → h b < h a
h-resp-< {a} {b} a<b = begin⟨ a<b ⟩
  ∴ a <ₐₚ b     $⟨ <ₐₚ⇒<ᵣ ⟩
  ∴ a <ᵣ  b     $⟨ ↑-resp-<ᵣ ⟩
  ∴ ↑ b ⊂ ↑ a   $⟨ length-mono-< 𝔸ₛ ⟩
  ∴ h b < h a   ∎

h-cong : a ≈ₐ b → h a ≡ h b
h-cong {a} {b} a≈b = begin⟨ a≈b ⟩
  ∴   a ≈ₐ  b  $⟨ ↑-cong ⟩
  ∴ ↑ a ≋ ↑ b  $⟨ ≋-length ⟩
  ∴ h a ≡ h b  ∎

heightFunction : HeightFunction algebra A
heightFunction = record
  { h         = h
  ; h-cong    = h-cong
  ; h-bounded = h-bounded
  ; h-resp-<  = h-resp-<
  ; h-resp-↝  = h-resp-↝
  }
