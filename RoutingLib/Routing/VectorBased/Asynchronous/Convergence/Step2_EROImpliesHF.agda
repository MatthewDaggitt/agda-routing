open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.InternalDefinitions

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  (finite : IsFinite algebra)
  {n} (A : AdjacencyMatrix algebra n)
  {ℓ₂} (extRespOrder : ExtensionRespectingOrder algebra A ℓ₂)
  where

open RawRoutingAlgebra algebra

open import Data.List
open import Data.Nat hiding (_≟_; _⊔_)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties hiding (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Setoid S
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Binary.Equality.Setoid S
  using (_≋_; ≋-length; ≋-refl)
open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid.Properties
open import Function using (_∘_; flip)
open import Level using (_⊔_)
open import Relation.Unary using () renaming (_⊆_ to _⇒_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)

open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties
import RoutingLib.Data.List.Relation.Binary.Equality.Setoid S as Eq
open import RoutingLib.Data.Fin.Properties
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid
import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid.Properties as FiniteProperties
open import RoutingLib.Function.Reasoning

open ExtensionRespectingOrder extRespOrder hiding (_≟_)
open Finite finite hiding (cong)
open FiniteProperties finite hiding (_≟_)
open import RoutingLib.Routing.AdjacencyMatrix.Definitions algebra A

------------------------------------------------------------------------
-- Properties

<ᵣ-resp₂-≈ : ∀ {w x y z} → w ≈ x → y ≈ z → w <ᵣ y → x <ᵣ z
<ᵣ-resp₂-≈ w≈y y≈z = <ᵣ-respʳ-≈ y≈z ∘ <ᵣ-respˡ-≈ w≈y

routes : List Route
routes = tabulate f⁻¹

∈-routes : ∀ x → x ∈ routes
∈-routes x = ∈-resp-≈ S (f⁻¹∘f x) (∈-tabulate⁺ S (f x))

↑_ : Route → List Route
↑ x = filter (x <ᵣ?_) routes

↑-cong : ∀ {x y} → x ≈ y → ↑ x ≋ ↑ y
↑-cong {x} {y} x≈y = Eq.filter⁺ (x <ᵣ?_) (y <ᵣ?_) (<ᵣ-resp₂-≈ x≈y) (<ᵣ-resp₂-≈ (≈-sym x≈y) ∘ ≈-sym) (≋-refl {x = routes})

h : Route → ℕ
h x = suc (length (↑ x))

1≤h : ∀ x → 1 ≤ h x
1≤h x = s≤s z≤n

h≤H : ∀ x → h x ≤ h 0#
h≤H x = begin⟨ (λ {y} → x<y⇒0<y {y}) ⟩
  ∴ (x <ᵣ_) ⇒ (0# <ᵣ_) $⟨ flip (filter⁺₂ S (x <ᵣ?_) (0# <ᵣ?_)) routes ⟩
  ∴ ↑ x     ⊆ ↑ 0#     $⟨ s≤s ∘ length-mono-≤ S ⟩
  ∴ h x     ≤ h 0#     ∎
  where
  x<y⇒0<y : ∀ {y} → x <ᵣ y → 0# <ᵣ y
  x<y⇒0<y {y} x<y with x ≟ 0# 
  ... | yes x≈0 = <ᵣ-respˡ-≈ x≈0 x<y
  ... | no  x≉0 = <ᵣ-trans (<ᵣ-min x≉0) x<y

h-resp-↝ : ∀ {x y} → x ↝ y → h y < h x
h-resp-↝ {x} {y} x↝y = begin⟨ ↝⇒<ᵣ x↝y , <ᵣ-irrefl ≈-refl ⟩
  ∴ (x <ᵣ y) × ¬ (y <ᵣ y) $⟨ filter-⊂ S _ <ᵣ-respʳ-≈ _ <ᵣ-respʳ-≈ (<ᵣ-trans (↝⇒<ᵣ x↝y)) (∈-routes y) ⟩
  ∴ ↑ y ⊂ ↑ x             $⟨ s≤s ∘ length-mono-< S ⟩
  ∴ h y < h x             ∎

h-resp-≤ : ∀ {x y} → x <₊ y → h y ≤ h x
h-resp-≤ {x} {y} = begin⟨_⟩
  ∴ x <₊ y     $⟨ (λ x<₊y → filter⁺₂ S (y <ᵣ?_) (x <ᵣ?_) (<₊∧<ᵣ⇒<ᵣ x<₊y) routes) ⟩
  ∴ ↑ y ⊆ ↑ x  $⟨ s≤s ∘ length-mono-≤ S ⟩
  ∴ h y ≤ h x  ∎

h-cong : ∀ {x y} → x ≈ y → h x ≡ h y
h-cong {x} {y} x≈y = begin⟨ x≈y ⟩
  ∴   x ≈ y   $⟨ ↑-cong ⟩
  ∴ ↑ x ≋ ↑ y $⟨ cong suc ∘ ≋-length ⟩
  ∴ h x ≡ h y ∎

heightFunction : HeightFunction algebra A
heightFunction = record
  { h        = h
  ; h-cong   = h-cong
  ; 1≤h      = 1≤h
  ; h≤H      = h≤H
  ; h-resp-≤ = h-resp-≤
  ; h-resp-↝ = h-resp-↝
  }
