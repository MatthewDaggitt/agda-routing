
open import Algebra.FunctionProperties using (RightIdentity; LeftIdentity)
open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Data.List using (List; length; filter)
open import Data.List.Any as Any using ()
open import Data.List.Properties using (length-filter)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary using (Decidable; Transitive; Antisymmetric; _Respects₂_; Preorder; Poset; Total)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.List.Enumeration
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Nat.Properties using (<⇒≱)
open import RoutingLib.Function.HeightFunction
open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.SufficientConditions

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Convergence.Step1_HeightFunction 
  {a b ℓ n-2} 
  (rp : RoutingProblem a b ℓ (suc n-2)) 
  (cc : ConvergenceConditions (RoutingProblem.ra rp))
  where
  
  open RoutingProblem rp
  open ConvergenceConditions cc

  open import RoutingLib.Data.List.All.Uniqueness S
  open import RoutingLib.Data.List.All.Uniqueness.Properties
  open import RoutingLib.Data.List.Any.GenericMembership S
  open Enumeration routes-enumerable renaming (list to routes)


  -- The concept of an element being below another in the left natural order induced by ⊕

  below : Route → Route → Bool
  below x y = ⌊ y ≤? x ⌋
    
  below-x≤y : ∀ {x y} → x ≤ y → below y x ≡ true
  below-x≤y {x} {y} x≤y with x ≤? y
  ... | yes _   = ≡-refl
  ... | no  x≰y = contradiction x≤y x≰y
  
  below-x≰y : ∀ {x y} → ¬ (x ≤ y) → below y x ≡ false
  below-x≰y {x} {y} x≰y with x ≤? y
  ... | yes x≤y = contradiction x≤y x≰y
  ... | no  _   = ≡-refl

  below-⇨ : ∀ {u v} → u ≤ v → ∀ {x} → below u x ≡ true → below v x ≡ true
  below-⇨ {u} u≤v {x} below[u,x]≡true with x ≤? u
  ... | yes x≤u = below-x≤y (≤-trans x≤u u≤v)
  ... | no  x≰u = contradiction below[u,x]≡true λ()
  
  below-cong : ∀ u {x y} → x ≈ y → below u x ≡ below u y
  below-cong u {x} {y} x≈y with x ≤? u | y ≤? u
  ... | no _ | no _ = ≡-refl
  ... | no x≰u | yes y≤u = contradiction (≤-respₗ-≈ (sym x≈y) y≤u) x≰u
  ... | yes x≤u | no y≰u = contradiction (≤-respₗ-≈ x≈y x≤u) y≰u
  ... | yes _ | yes _ = ≡-refl



  -- Down-set definitions and properties

  ↓_ : Route → List Route
  ↓ x = filter (below x) routes
    
  !↓_ : ∀ x → Unique (↓ x)
  !↓ x = filter! S (below x) unique

  x∈↓x : ∀ x → x ∈ (↓ x)
  x∈↓x x = ∈-filter (below-cong x) (complete x) (below-x≤y ≤-refl)

  x≤y⇨↓x⊆↓y : ∀ {x y} → x ≤ y → ↓ x ⊆ ↓ y
  x≤y⇨↓x⊆↓y x≤y = filter-⊆ routes (below-⇨ x≤y)



  -- Height function definition and properties

  height : Route → ℕ
  height x = length (↓ x)

  h[v]≤h[0] : ∀ {v} → height v ≤ℕ height 0#
  h[v]≤h[0] {v} = length-⊆ S (!↓ v) (x≤y⇨↓x⊆↓y (0#-idₗ-⊕ v))

  h-resp-≤ : ∀  {u v} → u ≤ v → height u ≤ℕ height v
  h-resp-≤ {u} u≤v = length-⊆ S (!↓ u) (x≤y⇨↓x⊆↓y u≤v)

  ≤-resp-h : ∀ {u v} → height u ≤ℕ height v → u ≤ v
  ≤-resp-h {u} {v} h[u]≤h[v] with u ≤? v
  ... | yes u≤v = u≤v
  ... | no  u≰v with ≤-total u v
  ...   | inj₁ u≤v = contradiction u≤v u≰v
  ...   | inj₂ v≤u = contradiction h[u]≤h[v] (<⇒≱ (length-⊂ S (!↓ v) (x≤y⇨↓x⊆↓y v≤u) (∉-filter (below-cong v) (below-x≰y u≰v) routes) (x∈↓x u)))



  -- We can now construct a bounded height function

  heightFunction : BoundedHeightFunction ≤-poset
  heightFunction = record {
      h = height;
      hₘₐₓ = height 0#;
      h≤hₘₐₓ = h[v]≤h[0];
      h-resp-≤ = h-resp-≤;
      ≤-resp-h = ≤-resp-h
   } 
