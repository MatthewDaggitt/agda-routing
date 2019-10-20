open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.HeightFunction
  {a b ℓ} (alg : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix alg n)
  where

open RawRoutingAlgebra alg

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
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; cong)

open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.ExtensionRespectingOrder
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties
import RoutingLib.Data.List.Relation.Binary.Equality.Setoid S as Eq
open import RoutingLib.Data.Fin.Properties
open import RoutingLib.Relation.Nullary
open import RoutingLib.Function.Reasoning

------------------------------------------------------------------------
-- Definition

record HeightFunction : Set (a ⊔ ℓ) where
  field
    h        : Route → ℕ
    1≤h      : ∀ x → 1 ≤ h x
    h≤H      : ∀ x → h x ≤ h 0#
    h-resp-▷ : ∀ x i j → h (A i j ▷ x) < h x
    h-resp-< : ∀ {x y} → x <₊ y → h y < h x
    h-cong   : ∀ {x y} → x ≈ y → h x ≡ h y

  H : ℕ
  H = h 0#

------------------------------------------------------------------------
-- Properties

module ExtensionRespecting⇒HeightFunction
  {ℓ₂} (extRespOrder : ExtensionRespectingOrder alg A ℓ₂) (finite : IsFinite alg) where

  open ExtensionRespectingOrder extRespOrder hiding (_≟_) renaming (_<_ to _<ʳ_; _<?_ to _<ʳ?_)
  open Finiteₛ finite hiding (_≟_; cong)
  
  <-resp₂-≈ : ∀ {w x y z} → w ≈ x → y ≈ z → w <ʳ y → x <ʳ z
  <-resp₂-≈ w≈y y≈z = <-respʳ-≈ y≈z ∘ <-respˡ-≈ w≈y
  
  routes : List Route
  routes = tabulate f⁻¹

  ∈-routes : ∀ x → x ∈ routes
  ∈-routes x = ∈-resp-≈ S (f⁻¹∘f x) (∈-tabulate⁺ S (f x))

  ↑_ : Route → List Route
  ↑ x = filter (x <ʳ?_) routes

  ↑-cong : ∀ {x y} → x ≈ y → ↑ x ≋ ↑ y
  ↑-cong {x} {y} x≈y = Eq.filter⁺ (x <ʳ?_) (y <ʳ?_) (<-resp₂-≈ x≈y) (<-resp₂-≈ (≈-sym x≈y) ∘ ≈-sym) (≋-refl {x = routes})
  
  h : Route → ℕ
  h x = suc (length (↑ x))

  1≤h : ∀ x → 1 ≤ h x
  1≤h x = s≤s z≤n

  h≤H : ∀ x → h x ≤ h 0#
  h≤H x = begin⟨ ⊆-refl ⟩
    ∴ routes ⊆ routes $⟨ filter⁺ S (x <ʳ?_) (0# <ʳ?_) test ⟩
    ∴ ↑ x ⊆ ↑ 0#      $⟨ s≤s ∘ length-mono-≤ S ⟩
    ∴ h x ≤ h 0#      ∎
    where
    test3 : ∀ {x y} → x <ʳ y → x ≉ y
    test3 {x} {y} x<y x≈y = irrefl x≈y x<y
    
    test2 : ∀ {x y} → x <ʳ y → 0# ≉ y
    test2 {x} {y} x<y with 0# ≟ x
    ... | yes 0≈x = flip irrefl (<-respˡ-≈ (≈-sym 0≈x) x<y)
    ... | no  0≉x = test3 (trans (<-min 0≉x) x<y)
    
    test : ∀ {y z} → y ≈ z → x <ʳ y → 0# <ʳ z
    test {y} {z} y≈z x<y = <-min (test2 (<-respʳ-≈ y≈z x<y))
    
  h-resp-▷ : ∀ x i j → h (A i j ▷ x) < h x
  h-resp-▷ x i j = begin⟨ x<Aᵢⱼ[x] , irrefl ≈-refl ⟩
    ∴ (x <ʳ Aᵢⱼ[x]) × ¬ (Aᵢⱼ[x] <ʳ Aᵢⱼ[x]) $⟨ filter-⊂ S _ <-respʳ-≈ _ <-respʳ-≈ (trans x<Aᵢⱼ[x]) (∈-routes Aᵢⱼ[x]) ⟩
    ∴ ↑ Aᵢⱼ[x] ⊂ ↑ x                       $⟨ s≤s ∘ length-mono-< S ⟩
    ∴ h Aᵢⱼ[x] < h x                       ∎
    where Aᵢⱼ[x] = A i j ▷ x; x<Aᵢⱼ[x] = ↝⇒< (i , j , ≈-refl)

  h-resp-< : ∀ {x y} → x <₊ y → h y < h x
  h-resp-< {x} {y} x<y = begin⟨ <₊⇒< x<y , irrefl ≈-refl ⟩
    ∴ (x <ʳ y) × ¬ (y <ʳ y)           $⟨ filter-⊂ S _ <-respʳ-≈ _ <-respʳ-≈ (trans (<₊⇒< x<y)) (∈-routes y) ⟩
    ∴ ↑ y ⊂ ↑ x                       $⟨ s≤s ∘ length-mono-< S ⟩
    ∴ h y < h x                       ∎
  
  h-cong : ∀ {x y} → x ≈ y → h x ≡ h y
  h-cong {x} {y} x≈y = begin⟨ x≈y ⟩
    ∴   x ≈ y   $⟨ ↑-cong ⟩
    ∴ ↑ x ≋ ↑ y $⟨ cong suc ∘ ≋-length ⟩
    ∴ h x ≡ h y ∎
  
  heightFunction : HeightFunction
  heightFunction = record
    { h        = h
    ; h-cong   = h-cong
    ; 1≤h      = 1≤h
    ; h≤H      = h≤H
    ; h-resp-< = h-resp-<
    ; h-resp-▷ = h-resp-▷
    }

open ExtensionRespecting⇒HeightFunction public
  using () renaming (heightFunction to extRespOrder⇒heightFunction)
