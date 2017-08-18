open import Data.Product using (∃; ∃₂; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n; suc-injective; ≤-trans; ≤-refl; ≤-reflexive; ≰⇒≥; +-comm; +-assoc; +-mono-≤; ∸-mono; m≤m⊔n; ⊔-mono-≤; ⊓-mono-≤; m⊓n≤m; ⊓-idem; ⊓-assoc; ⊔-identityʳ; ⊓-comm; +-cancelˡ-≡; +-distribˡ-⊔; n≤m⊔n; +-monoʳ-<; <⇒≤;  module ≤-Reasoning)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
  renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)
open import Function using (_∘_; _$_)

open import RoutingLib.Data.Graph.SimplePath using (SimplePath; length)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m+o≡n; ∸-distribˡ-⊓-⊔; n⊓-mono-≤; ⊓n-mono-≤; m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; ∸-monoˡ-<; m≤n⇒m⊓n≡m; ∸-cancelˡ; n<m⇒n⊓o<m; ⊓-triangulate; n≢0⇒0<n; ≤-stepsʳ)
open import RoutingLib.Data.Matrix using (min⁺; map)
open import RoutingLib.Data.Matrix.Properties using (min⁺-cong; min⁺-constant; min⁺[M]≤x)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (min⁺[M]∈M)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)
import RoutingLib.Routing.BellmanFord.PathsConvergence.Prelude as Prelude

module RoutingLib.Routing.BellmanFord.PathsConvergence.Step1_Ultrametric
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (sc : SufficientConditions 𝓡𝓐)
  {n-1 : ℕ} 
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) (suc n-1))
  where

  open SufficientConditions sc
  open Prelude  𝓡𝓐 ⊕-sel G
  
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_UltrametricAlt 𝓡𝓟ᶜ (convertSufficientConditions sc) using () renaming (d to dᶜ; dₛᵤₚ to dᶜₛᵤₚ; d≡0⇒X≈Y to dᶜ≡0⇒X≈Y; X≈Y⇒d≡0 to X≈Y⇒dᶜ≡0; d-sym to dᶜ-sym; d-cong₂ to dᶜ-cong; d-maxTriIneq to dᶜ-maxTriIneq; d≤dₛᵤₚ to dᶜ≤dᶜₛᵤₚ; d≤dₘₐₓ to dᶜ≤dᶜₘₐₓ)

  n : ℕ
  n = suc n-1

  sizeⁱ≤n-1 : ∀ r → sizeⁱ r ≤ n-1
  sizeⁱ≤n-1 r = ≤-pred (sizeⁱ<n ≡-refl r)

  ------------------------------------------------------------------------------
  -- Inconsistent length
  ------------------------------------------------------------------------------
  -- The size of inconsistent routes where consistent routes are viewed as
  -- having the maximum size `n-1`
  
  lengthⁱ : IRoute → ℕ
  lengthⁱ r with 𝑪? r
  ... | yes _ = n-1
  ... | no  _ = sizeⁱ r

  lengthⁱ≡n-1 : ∀ {r} → 𝑪 r → lengthⁱ r ≡ n-1
  lengthⁱ≡n-1 {r} rᶜ with 𝑪? r
  ... | yes _  = ≡-refl
  ... | no  rⁱ = contradiction rᶜ rⁱ

  lengthⁱ≡size[r] : ∀ {r} → 𝑰 r → lengthⁱ r ≡ sizeⁱ r
  lengthⁱ≡size[r] {r} rⁱ with 𝑪? r
  ... | yes rᶜ = contradiction rᶜ rⁱ
  ... | no  _  = ≡-refl

  lengthⁱ-cong : ∀ {r s} → r ≈ⁱ s → lengthⁱ r ≡ lengthⁱ s
  lengthⁱ-cong {r} {s} r≈s with 𝑪? r | 𝑪? s
  ... | yes _  | yes _  = ≡-refl
  ... | no  rⁱ | yes sᶜ = contradiction (𝑪-cong sᶜ (≈ⁱ-sym r≈s)) rⁱ
  ... | yes rᶜ | no  sⁱ = contradiction (𝑪-cong rᶜ r≈s) sⁱ
  ... | no  _  | no  _  = size-cong r≈s

  lengthⁱ≤n-1 : ∀ r → lengthⁱ r ≤ n-1
  lengthⁱ≤n-1 r with 𝑪? r
  ... | yes _ = ≤-refl
  ... | no  _ = sizeⁱ≤n-1 r

  lengthⁱ≡|p| : ∀ {r} → 𝑰 r → ∃ λ (p : SimplePath n) → lengthⁱ r ≡ length p
  lengthⁱ≡|p| {inull}      rⁱ = contradiction 𝒄-null rⁱ
  lengthⁱ≡|p| {iroute x p} rⁱ with 𝑪? (iroute x p)
  ... | yes rᶜ = contradiction rᶜ rⁱ  
  ... | no  _  = p , ≡-refl

  ------------------------------------------------------------------------------
  -- Shortest inconsistent route
  ------------------------------------------------------------------------------
  -- The length of the shortest inconsistent route in X
  
  shortest : IMatrix → ℕ
  shortest X = min⁺ (map lengthⁱ X)

  shortest-cong : ∀ {X Y} → X ≈ⁱₘ Y → shortest X ≡ shortest Y
  shortest-cong X≈Y = min⁺-cong (λ i j → lengthⁱ-cong (X≈Y i j))

  shX<n : ∀ X → shortest X < n
  shX<n X = s≤s (min⁺[M]≤x (map lengthⁱ X) (fzero , fzero , lengthⁱ≤n-1 (X fzero fzero)))

  postulate shXⁱ≡|Xⁱᵢⱼ| : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → shortest X ≡ sizeⁱ (X i j) × 𝑰 (X i j)
  {-
  shXⁱ≡|Xⁱᵢⱼ| {X} ¬Xᶜ with min+∈M (map sizeⁱ X)
  ... | i , j , shX≡|Xᵢⱼ| = i , j , shX≡|Xᵢⱼ| , {!!}
  -}
    
  shXⁱ≡|p| : ∀ {X} → 𝑰ₘ X → ∃₂ λ x (p : SimplePath n) → shortest X ≡ length p × 𝑰 (iroute x p)
  shXⁱ≡|p| {X} Xⁱ with shXⁱ≡|Xⁱᵢⱼ| Xⁱ
  ... | i , j , shX≡|Xᵢⱼ| , Xᵢⱼⁱ with X i j | 𝑪? (X i j)
  ...   | inull      | _       = contradiction 𝒄-null Xᵢⱼⁱ
  ...   | iroute x p | yes Xᵢⱼᶜ = contradiction Xᵢⱼᶜ Xᵢⱼⁱ
  ...   | iroute x p | no  _   = x , p , shX≡|Xᵢⱼ| , Xᵢⱼⁱ

  postulate shX⊓shY≡|p| : ∀ X Y → 𝑰ₘ X ⊎ 𝑰ₘ Y →
                          ∃ λ (p : SimplePath n) → shortest X ⊓ shortest Y ≡ length p
    
  Xᶜ⇒shX≡n-1 : ∀ {X} → 𝑪ₘ X → shortest X ≡ n-1
  Xᶜ⇒shX≡n-1 Xᶜ = min⁺-constant (λ i j → lengthⁱ≡n-1 (Xᶜ i j))

  Yᶜ⇒shX≤shY : ∀ X {Y} → 𝑪ₘ Y → shortest X ≤ shortest Y
  Yᶜ⇒shX≤shY X Yᶜ = ≤-trans (≤-pred (shX<n X)) (≤-reflexive (≡-sym (Xᶜ⇒shX≡n-1 Yᶜ)))

  Yᶜ⇒shX⊓shY≡shX : ∀ X {Y} → 𝑪ₘ Y → shortest X ⊓ shortest Y ≡ shortest X
  Yᶜ⇒shX⊓shY≡shX X Yᶜ = m≤n⇒m⊓n≡m (Yᶜ⇒shX≤shY X Yᶜ)
    
  Xᶜ⇒shX⊓shY≡shY : ∀ {X} Y → 𝑪ₘ X → shortest X ⊓ shortest Y ≡ shortest Y
  Xᶜ⇒shX⊓shY≡shY Y Xᶜ = ≡-trans (⊓-comm _ (shortest Y)) (Yᶜ⇒shX⊓shY≡shX Y Xᶜ)

  shX⊓shY<n : ∀ X Y → shortest X ⊓ shortest Y < n
  shX⊓shY<n X Y = n<m⇒n⊓o<m (shortest Y) (shX<n X)

  ------------------------------------------------------------------------------
  -- Mapping length into the right range
  ------------------------------------------------------------------------------
  -- Maps a path length to the corresponding distance
  
  invert : ℕ → ℕ
  invert x = dᶜₛᵤₚ + (n ∸ x)

  invert-≤ : ∀ {x y} → y ≤ x → invert x ≤ invert y
  invert-≤ y≤x = +-mono-≤ {dᶜₛᵤₚ} ≤-refl (∸-mono ≤-refl y≤x)
  
  invert-< : ∀ {x y} → y < x → x < n → invert x < invert y
  invert-< y<x x<n = +-monoʳ-< {dᶜₛᵤₚ} ≤-refl (∸-monoˡ-< y<x x<n)

  invert-<sh : ∀ {X Y} → shortest Y < shortest X → invert (shortest X) < invert (shortest Y)
  invert-<sh {X} shY<shX = invert-< shY<shX (shX<n X)
  
  invert-¬cong : ∀ {x y} → x ≤ n → y ≤ n → x ≢ y → invert x ≢ invert y
  invert-¬cong x≤n y≤n x≢y ix≡iy = x≢y (∸-cancelˡ x≤n y≤n (+-cancelˡ-≡ dᶜₛᵤₚ ix≡iy))

  invert-distr2 : ∀ x y → invert (x ⊓ y) ≡ invert x ⊔ invert y
  invert-distr2 x y = begin
    dᶜₛᵤₚ + (n ∸ (x ⊓ y))       ≡⟨ cong (dᶜₛᵤₚ +_) (∸-distribˡ-⊓-⊔ n x y) ⟩
    dᶜₛᵤₚ + ((n ∸ x) ⊔ (n ∸ y)) ≡⟨ +-distribˡ-⊔ dᶜₛᵤₚ _ _ ⟩
    invert x ⊔ invert y ∎
    where open ≡-Reasoning
    
  invert-distr : ∀ X Y Z → invert (shortest X ⊓ shortest Y ⊓ shortest Z) ≡ invert (shortest X ⊓ shortest Y) ⊔ invert (shortest Y ⊓ shortest Z)
  invert-distr X Y Z = begin
    invert (sh X ⊓ sh Y ⊓ sh Z)                  ≡⟨ cong invert (⊓-triangulate (sh X) _ _) ⟩
    invert ((sh X ⊓ sh Y) ⊓ (sh Y ⊓ sh Z))       ≡⟨ invert-distr2 (sh X ⊓ sh Y) (sh Y ⊓ sh Z) ⟩
    invert (sh X ⊓ sh Y) ⊔ invert (sh Y ⊓ sh Z)  ∎
    where open ≡-Reasoning ; sh = shortest

  
  ------------------------------------------------------------------------------
  -- Distance metric for inconsistent IMatrices
  ------------------------------------------------------------------------------

  dⁱ : IMatrix → IMatrix → ℕ
  dⁱ X Y = invert (shortest X ⊓ shortest Y)

  dⁱ-sym : ∀ X Y → dⁱ X Y ≡ dⁱ Y X
  dⁱ-sym X Y = cong invert (⊓-comm (shortest X) (shortest Y))

  dⁱ-cong : ∀ {W X Y Z} → W ≈ⁱₘ Y → X ≈ⁱₘ Z → dⁱ W X ≡ dⁱ Y Z
  dⁱ-cong W≈Y X≈Z = cong invert
    (cong₂ _⊓_ (shortest-cong W≈Y) (shortest-cong X≈Z))

  dⁱ-maxTriangleIneq : MaxTriangleIneq ℝ𝕄ⁱₛ dⁱ
  dⁱ-maxTriangleIneq X Y Z = begin
    invert (sh X ⊓ sh Z)                        ≤⟨ invert-≤ (⊓-mono-≤ (m⊓n≤m (shortest X) _) ≤-refl) ⟩
    invert (sh X ⊓ sh Y ⊓ sh Z)                 ≡⟨ cong invert (⊓-triangulate (sh X) _ _) ⟩
    invert ((sh X ⊓ sh Y) ⊓ (sh Y ⊓ sh Z))      ≡⟨ invert-distr2 (sh X ⊓ sh Y) (sh Y ⊓ sh Z) ⟩
    invert (sh X ⊓ sh Y) ⊔ invert (sh Y ⊓ sh Z) ∎
    where open ≤-Reasoning ; sh = shortest

  dᶜ<dⁱ : ∀ W X Y Z → dᶜ W X < dⁱ Y Z
  dᶜ<dⁱ W X Y Z = s≤s (≤-stepsʳ _ (dᶜ≤dᶜₘₐₓ W X))
  
  Xᶜ⇒dⁱXZ≤dⁱYZ : ∀ {X} → 𝑪ₘ X → ∀ Y Z → dⁱ X Z ≤ dⁱ Y Z
  Xᶜ⇒dⁱXZ≤dⁱYZ Xᶜ Y Z = invert-≤ (⊓n-mono-≤ (shortest Z) (Yᶜ⇒shX≤shY Y Xᶜ))

  Yᶜ⇒dⁱXY≤dⁱXZ : ∀ X {Y} → 𝑪ₘ Y → ∀ Z → dⁱ X Y ≤ dⁱ X Z
  Yᶜ⇒dⁱXY≤dⁱXZ X Yᶜ Z = invert-≤ (n⊓-mono-≤ (shortest X) (Yᶜ⇒shX≤shY Z Yᶜ))
  
  ------------------------------------------------------------------------------
  -- Pseudo-distance function
  ------------------------------------------------------------------------------
  -- A pseudo-distance function over IMatrices
  -- (doesn't obey the equality metric axioms)
  
  dₕ : IMatrix → IMatrix → ℕ
  dₕ X Y with 𝑪ₘ? X | 𝑪ₘ? Y
  ... | no _   | _     = dⁱ X Y
  ... | _      | no _  = dⁱ X Y
  ... | yes Xᶜ | yes Yᶜ = dᶜ (fromIₘ Xᶜ) (fromIₘ Yᶜ)

  dₕ-sym : ∀ X Y → dₕ X Y ≡ dₕ Y X
  dₕ-sym X Y with 𝑪ₘ? X | 𝑪ₘ? Y
  ... | no  _ | no  _ = dⁱ-sym X Y
  ... | no  _ | yes _ = dⁱ-sym X Y
  ... | yes _ | no  _ = dⁱ-sym X Y
  ... | yes _ | yes _ = dᶜ-sym (fromIₘ _) (fromIₘ _)
  
  dₕ-cong : ∀ {W X Y Z} → W ≈ⁱₘ Y → X ≈ⁱₘ Z → dₕ W X ≡ dₕ Y Z
  dₕ-cong {W} {X} {Y} {Z} W≈Y X≈Z with 𝑪ₘ? W | 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ... | yes Wᶜ | _      | no  Yⁱ | _      = contradiction (𝑪ₘ-cong Wᶜ W≈Y) Yⁱ
  ... | no  Wⁱ | _      | yes Yᶜ | _      = contradiction (𝑪ₘ-cong Yᶜ (≈ⁱₘ-sym W≈Y)) Wⁱ
  ... | _      | yes Xᶜ | _      | no  Zⁱ = contradiction (𝑪ₘ-cong Xᶜ X≈Z) Zⁱ
  ... | _      | no  Xⁱ | _      | yes Zᶜ = contradiction (𝑪ₘ-cong Zᶜ (≈ⁱₘ-sym X≈Z)) Xⁱ
  ... | yes _  | yes _  | yes _  | yes _  = dᶜ-cong (fromIₘ-cong _ _ W≈Y) (fromIₘ-cong _ _ X≈Z)
  ... | yes _  | no  _  | yes _  | no  _  = dⁱ-cong W≈Y X≈Z
  ... | no  _  | yes _  | no  _  | yes _  = dⁱ-cong W≈Y X≈Z
  ... | no  _  | no  _  | no  _  | no  _  = dⁱ-cong W≈Y X≈Z

  dₕ-maxTriIneq : MaxTriangleIneq ℝ𝕄ⁱₛ dₕ
  dₕ-maxTriIneq X Y Z with 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ... | yes _  | yes _ | yes _  = dᶜ-maxTriIneq _ _ _
  ... | yes Xᶜ | yes _ | no  _  = m≤o⇒m≤n⊔o (dᶜ _ _) (Xᶜ⇒dⁱXZ≤dⁱYZ Xᶜ Y Z)
  ... | no  _  | yes _ | yes Zᶜ = m≤n⇒m≤n⊔o (dᶜ _ _) (Yᶜ⇒dⁱXY≤dⁱXZ X Zᶜ Y)
  ... | yes _  | no  _ | yes _  = m≤n⇒m≤n⊔o (dⁱ Y Z) (<⇒≤ (dᶜ<dⁱ _ _ X Y))
  ... | yes _  | no  _ | no  _  = dⁱ-maxTriangleIneq X Y Z
  ... | no  _  | yes _ | no  _  = dⁱ-maxTriangleIneq X Y Z
  ... | no  _  | no  _ | yes _  = dⁱ-maxTriangleIneq X Y Z
  ... | no  _  | no  _ | no  _  = dⁱ-maxTriangleIneq X Y Z

    
  X≉Y⇒dₕ≢0 : ∀ {X Y} → X ≉ⁱₘ Y → dₕ X Y ≢ 0
  X≉Y⇒dₕ≢0 {X} {Y} X≉Y dₕ≡0 with 𝑪ₘ? X | 𝑪ₘ? Y
  ... | no  _ | _     = contradiction dₕ≡0 λ()
  ... | yes _ | no  _ = contradiction dₕ≡0 λ()
  ... | yes _ | yes _ = contradiction (dᶜ≡0⇒X≈Y dₕ≡0) (fromIₘ-¬cong _ _ X≉Y)
    
  dₕ≡dⁱ : ∀ X Y → 𝑰ₘ X ⊎ 𝑰ₘ Y → dₕ X Y ≡ dⁱ X Y
  dₕ≡dⁱ X Y ¬Xᶜ⊎¬Yᶜ with 𝑪ₘ? X | 𝑪ₘ? Y
  ... | no  _  | _     = ≡-refl
  ... | yes _  | no  _ = ≡-refl
  ... | yes Xᶜ | yes Yᶜ = contradiction ¬Xᶜ⊎¬Yᶜ [ _$ Xᶜ , _$ Yᶜ ]′
    
  X≉Y⇒0<dₕ : ∀ {X Y} → X ≉ⁱₘ Y → zero < dₕ X Y
  X≉Y⇒0<dₕ {X} {Y} X≉Y with 𝑪ₘ? X | 𝑪ₘ? Y
  ... | no  _  | _      = s≤s z≤n
  ... | yes _  | no  _  = s≤s z≤n
  ... | yes Xᶜ | yes Yᶜ with dᶜ (fromIₘ Xᶜ) (fromIₘ Yᶜ) ≟ℕ 0
  ...   | yes dᶜ≡0 = contradiction (dᶜ≡0⇒X≈Y dᶜ≡0) (fromIₘ-¬cong Xᶜ Yᶜ X≉Y)
  ...   | no  dᶜ≢0 = n≢0⇒0<n dᶜ≢0

  ------------------------------------------------------------------------------
  -- Distance function
  ------------------------------------------------------------------------------
  -- A true distance function over IMatrices
  d : IMatrix → IMatrix → ℕ
  d X Y with X ≟ⁱₘ Y
  ... | yes _ = zero
  ... | no  _ = dₕ X Y

  d-sym : ∀ X Y → d X Y ≡ d Y X
  d-sym X Y with X ≟ⁱₘ Y | Y ≟ⁱₘ X
  ... | yes _   | yes _   = ≡-refl
  ... | no  X≉Y | yes Y≈X = contradiction (≈ⁱₘ-sym Y≈X) X≉Y
  ... | yes X≈Y | no  Y≉X = contradiction (≈ⁱₘ-sym X≈Y) Y≉X
  ... | no  _   | no  _   = dₕ-sym X Y

  d-cong : d Preserves₂ _≈ⁱₘ_ ⟶ _≈ⁱₘ_ ⟶ _≡_
  d-cong {W} {X} {Y} {Z} W≈X Y≈Z with W ≟ⁱₘ Y | X ≟ⁱₘ Z
  ... | no  _   | no _    = dₕ-cong W≈X Y≈Z
  ... | no  W≉Y | yes X≈Z = contradiction (≈ⁱₘ-trans (≈ⁱₘ-trans W≈X X≈Z) (≈ⁱₘ-sym Y≈Z)) W≉Y
  ... | yes W≈Y | no  X≉Z = contradiction (≈ⁱₘ-trans (≈ⁱₘ-trans (≈ⁱₘ-sym W≈X) W≈Y) Y≈Z) X≉Z
  ... | yes _   | yes _   = ≡-refl

  d-maxTriIneq : MaxTriangleIneq ℝ𝕄ⁱₛ d
  d-maxTriIneq X Y Z with X ≟ⁱₘ Z | X ≟ⁱₘ Y | Y ≟ⁱₘ Z
  ... | yes _   | _       | _       = z≤n
  ... | no  X≉Z | yes X≈Y | yes Y≈Z = contradiction (≈ⁱₘ-trans X≈Y Y≈Z) X≉Z
  ... | no  _   | yes X≈Y | no  _   = ≤-reflexive (dₕ-cong X≈Y ≈ⁱₘ-refl)
  ... | no  _   | no  _   | no  _   = dₕ-maxTriIneq X Y Z
  ... | no  _   | no  _   | yes Y≈Z =
    m≤n⇒m≤n⊔o zero (≤-reflexive (dₕ-cong ≈ⁱₘ-refl (≈ⁱₘ-sym Y≈Z)))
  
  X≈Y⇒d≡0 : ∀ {X Y} → X ≈ⁱₘ Y → d X Y ≡ 0
  X≈Y⇒d≡0 {X} {Y} X≈Y with X ≟ⁱₘ Y
  ... | yes _   = ≡-refl
  ... | no  X≉Y = contradiction X≈Y X≉Y

  d≡0⇒X≈Y : ∀ {X Y} → d X Y ≡ 0 → X ≈ⁱₘ Y
  d≡0⇒X≈Y {X} {Y} d≡0 with X ≟ⁱₘ Y
  ... | yes X≈Y = X≈Y
  ... | no  X≉Y = contradiction d≡0 (X≉Y⇒dₕ≢0 X≉Y)

  d≡dₕ : ∀ {X Y} → X ≉ⁱₘ Y → d X Y ≡ dₕ X Y
  d≡dₕ {X} {Y} X≉Y with X ≟ⁱₘ Y
  ... | yes X≈Y = contradiction X≈Y X≉Y
  ... | no  _   = ≡-refl
    
  d≡dⁱ : ∀ {X Y} → X ≉ⁱₘ Y → 𝑰ₘ X ⊎ 𝑰ₘ Y →
                      d X Y ≡ invert (shortest X ⊓ shortest Y)
  d≡dⁱ X≉Y ¬Xᶜ⊎¬Yᶜ = ≡-trans (d≡dₕ X≉Y) (dₕ≡dⁱ _ _ ¬Xᶜ⊎¬Yᶜ)
    
  d≡inv|p| : ∀ {X Y} → X ≉ⁱₘ Y → 𝑰ₘ X ⊎ 𝑰ₘ Y →
                ∃ λ (p : SimplePath n) → d X Y ≡ invert (length p)
  d≡inv|p| {X} {Y} X≉Y Xⁱ⊎Yⁱ with shX⊓shY≡|p| X Y Xⁱ⊎Yⁱ
  ... | p , shX⊓shY≡|p| = p , ≡-trans (d≡dⁱ X≉Y Xⁱ⊎Yⁱ) (cong invert shX⊓shY≡|p|)

  d≡dᶜ : ∀ X Y → d (toIₘ X) (toIₘ Y) ≡ dᶜ X Y
  d≡dᶜ X Y with toIₘ X ≟ⁱₘ toIₘ Y
  ... | yes toX≈toY = ≡-sym (X≈Y⇒dᶜ≡0 (toIₘ-injective toX≈toY))
  ... | no  toX≉toY with 𝑪ₘ? (toIₘ X) | 𝑪ₘ? (toIₘ Y)
  ...   | no  toXⁱ | _        = contradiction (toIₘᶜ X) toXⁱ
  ...   | _        | no  toYⁱ = contradiction (toIₘᶜ Y) toYⁱ
  ...   | yes toXᶜ | yes toYᶜ  = dᶜ-cong (fromIₘ-toIₘ toXᶜ) (fromIₘ-toIₘ toYᶜ)
  
  d-isUltrametric : IsUltrametric ℝ𝕄ⁱₛ d
  d-isUltrametric = record 
    { eq⇒0        = X≈Y⇒d≡0
    ; 0⇒eq        = d≡0⇒X≈Y
    ; sym         = d-sym
    ; maxTriangle = d-maxTriIneq
    }

