open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n; ≤+≢⇒<; suc-injective; ≤-trans; ≤-refl; ≤-reflexive; <-transʳ; <-transˡ; <-irrefl; ≤-antisym; ⊓-sel; ≰⇒≥; +-comm; +-assoc; +-mono-≤; ∸-mono; m≤m⊔n; ⊔-mono-≤; ⊓-mono-≤; m⊓n≤m; ⊓-idem; ⊓-assoc; ⊔-identityʳ; ⊓-comm; +-cancelˡ-≡; +-distribˡ-⊔; n≤m⊔n; +-monoʳ-<; <⇒≤; +-distribʳ-⊔; +-suc;  module ≤-Reasoning)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)
open import Function using (_∘_; _$_; id)

open import RoutingLib.Data.Graph.SimplePath using (SimplePath) renaming (length to lengthₚ)
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Graph
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m+o≡n; ∸-distribˡ-⊓-⊔; ⊔-monoˡ-≤; m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; +-monoʳ-≤; ≤-stepsˡ; ∸-monoˡ-<; m≤n⇒m⊓n≡m; ∸-cancelˡ; n<m⇒n⊓o<m; ⊔-triangulate; n≢0⇒0<n; ≤-stepsʳ; m>n⇒m∸n≢0; m<n⇒n≢0)
open import RoutingLib.Data.Matrix using (min⁺; map; max⁺; zipWith)
open import RoutingLib.Data.Matrix.Properties using (min⁺-cong; max⁺-constant; zipWith-sym; max⁺-cong; max⁺[M]≤max⁺[N]; M≤max⁺[M]; max⁺[M]-distrib-⊔)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Function using (_∘₂_)
open import RoutingLib.Function.Distance using (IsUltrametric; MaxTriangleIneq)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step1_HeightFunction as Step1
import RoutingLib.Routing.BellmanFord.DistanceVector.Step2_Ultrametric as Step2ᶜ

module RoutingLib.Routing.BellmanFord.PathVector.Step2_Ultrametric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒

  open Step1 𝓟𝓢𝓒
  
  open Step2ᶜ 𝓡𝓟ᶜ 𝓢𝓒
    using ()
    renaming
    ( D            to Dᶜ
    ; Dₛᵤₚ         to Dᶜₛᵤₚ
    ; Dₘₐₓ         to Dᶜₘₐₓ
    ; D≡0⇒X≈Y      to Dᶜ≡0⇒X≈Y
    ; X≈Y⇒D≡0      to X≈Y⇒Dᶜ≡0
    ; D-sym        to Dᶜ-sym
    ; D-cong₂      to Dᶜ-cong
    ; D-maxTriIneq to Dᶜ-maxTriIneq
    ; D≤Dₛᵤₚ       to Dᶜ≤Dᶜₛᵤₚ
    ; D≤dₘₐₓ       to Dᶜ≤Dᶜₘₐₓ
    ; 1≤Dₘₐₓ       to 1≤Dᶜₘₐₓ
    )

  abstract

    Hᶜ : ℕ
    Hᶜ = Dᶜₘₐₓ

    1≤Hᶜ : 1 ≤ Hᶜ
    1≤Hᶜ = 1≤Dᶜₘₐₓ

    Dᶜ≤Hᶜ : ∀ X Y → Dᶜ X Y ≤ Hᶜ
    Dᶜ≤Hᶜ = Dᶜ≤Dᶜₘₐₓ
{-
    hⁱx≤Hᶜ+Hⁱ : ∀ x → hⁱ x < Hᶜ + Hⁱ
    hⁱx≤Hᶜ+Hⁱ x = +-mono-≤ 1≤Dᶜₘₐₓ (hⁱ[r]≤n x)
-}

  ------------------------------------------------------------------------------
  -- Mapping length into the right range
  ------------------------------------------------------------------------------
  -- Maps a path length to the corresponding distance
  
    invert : ℕ → ℕ
    invert x = Hⁱ ∸ x

    invert-≤ : ∀ {x y} → y ≤ x → invert x ≤ invert y
    invert-≤ y≤x = ∸-mono ≤-refl y≤x
  
    invert-< : ∀ {x y} → y < x → x < n → invert x < invert y
    invert-< {x} {y} y<x x<n = ∸-monoˡ-< y<x x<n
  
    invert-¬cong : ∀ {x y} → x ≤ n → y ≤ n → x ≢ y → invert x ≢ invert y
    invert-¬cong x≤n y≤n x≢y = x≢y ∘ ∸-cancelˡ x≤n y≤n

{-
    invert≢0 : ∀ {x} → x < Hⁱ → invert x ≢ 0
    invert≢0 x<Hⁱ = m>n⇒m∸n≢0 x<Hⁱ
-}

{-
  invert-distr : ∀ X Y Z → invert (⟪ X ⟫ ⊓ ⟪ Y ⟫ ⊓ ⟪ Z ⟫) ≡
                           invert (⟪ X ⟫ ⊓ ⟪ Y ⟫) ⊔ invert (⟪ Y ⟫ ⊓ ⟪ Z ⟫)
  invert-distr X Y Z = begin
    invert (⟪ X ⟫ ⊓ ⟪ Y ⟫ ⊓ ⟪ Z ⟫)                  ≡⟨ cong invert (⊓-triangulate (⟪ X ⟫) _ _) ⟩
    invert ((⟪ X ⟫ ⊓ ⟪ Y ⟫) ⊓ (⟪ Y ⟫ ⊓ ⟪ Z ⟫))       ≡⟨ invert-distr2 (⟪ X ⟫ ⊓ ⟪ Y ⟫) (⟪ Y ⟫ ⊓ ⟪ Z ⟫) ⟩
    invert (⟪ X ⟫ ⊓ ⟪ Y ⟫) ⊔ invert (⟪ Y ⟫ ⊓ ⟪ Z ⟫)  ∎
    where open ≡-Reasoning
-}

  ------------------------------------------------------------------------------
  -- Distance metric for inconsistent routes
  ------------------------------------------------------------------------------

  abstract
  
    dⁱ : Route → Route → ℕ
    dⁱ x y with x ≟ y
    ... | yes _ = 0
    ... | no  _ = Hⁱ ∸ (hⁱ x ⊓ hⁱ y)
  
    dⁱ-cong : dⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
    dⁱ-cong {u} {v} {x} {y} u≈v x≈y with u ≟ x | v ≟ y
    ... | yes _   | yes _   = refl
    ... | yes u≈x | no  v≉y = contradiction (≈-trans (≈-trans (≈-sym u≈v) u≈x) x≈y) v≉y
    ... | no  u≉x | yes v≈y = contradiction (≈-trans (≈-trans u≈v v≈y) (≈-sym x≈y)) u≉x
    ... | no  _   | no  _   = cong₂ (invert ∘₂ _⊓_) (hⁱ-cong u≈v) (hⁱ-cong x≈y)

    x≈y⇒dⁱ≡0 : ∀ {x y} → x ≈ y → dⁱ x y ≡ 0
    x≈y⇒dⁱ≡0 {x} {y} x≈y with x ≟ y
    ... | yes _   = refl
    ... | no  x≉y = contradiction x≈y x≉y

    dⁱ≡0⇒x≈y : ∀ {x y} → dⁱ x y ≡ 0 → x ≈ y
    dⁱ≡0⇒x≈y {x} {y} dⁱxy≡0 with x ≟ y
    ... | yes x≈y = x≈y
    ... | no  _   = contradiction dⁱxy≡0 (m>n⇒m∸n≢0 (n<m⇒n⊓o<m _ (s≤s (hⁱ≤n-1 x))))
    
    dⁱ-sym : ∀ x y → dⁱ x y ≡ dⁱ y x
    dⁱ-sym x y with x ≟ y | y ≟ x
    ... | yes _   | yes _   = refl
    ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
    ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
    ... | no  _   | no  _   = cong invert (⊓-comm (hⁱ x) (hⁱ y))
  
    dⁱ-maxTriIneq : MaxTriangleIneq S dⁱ
    dⁱ-maxTriIneq x y z with x ≟ z | x ≟ y | y ≟ z
    ... | yes _   | _       | _       = z≤n
    ... | no  x≉z | yes x≈y | yes y≈z = contradiction (≈-trans x≈y y≈z) x≉z
    ... | no  _   | yes x≈y | no  _   = ≤-reflexive (cong (λ v → invert (v ⊓ hⁱ z)) (hⁱ-cong x≈y))
    ... | no  _   | no  _   | yes y≈z = ≤-reflexive (trans (cong (λ v → invert (hⁱ x ⊓ v)) (hⁱ-cong (≈-sym y≈z))) (sym (⊔-identityʳ _) ))
    ... | no  _   | no  _   | no  _   = begin
      invert (hⁱ x ⊓ hⁱ z)                                              ≡⟨ ∸-distribˡ-⊓-⊔ _ (hⁱ x) (hⁱ z) ⟩
      invert (hⁱ x) ⊔ invert (hⁱ z)                                     ≤⟨ ⊔-monoˡ-≤ (invert (hⁱ z)) (m≤m⊔n (invert (hⁱ x)) (invert (hⁱ y))) ⟩
      (invert (hⁱ x) ⊔ invert (hⁱ y)) ⊔ invert (hⁱ z)                   ≡⟨ ⊔-triangulate (invert (hⁱ x)) (invert (hⁱ y)) (invert (hⁱ z)) ⟩
      (invert (hⁱ x) ⊔ invert (hⁱ y)) ⊔ (invert (hⁱ y) ⊔ invert (hⁱ z)) ≡⟨ sym (cong₂ _⊔_ (∸-distribˡ-⊓-⊔ _ (hⁱ x) (hⁱ y)) (∸-distribˡ-⊓-⊔ _ (hⁱ y) (hⁱ z))) ⟩
      invert (hⁱ x ⊓ hⁱ y) ⊔ invert (hⁱ y ⊓ hⁱ z)                       ∎
      where open ≤-Reasoning

  ------------------------------------------------------------------------------
  -- Distance metric for inconsistent routes
  ------------------------------------------------------------------------------

  abstract
  
    Dⁱ : RMatrix → RMatrix → ℕ
    Dⁱ X Y = max⁺ (zipWith dⁱ X Y)
    
    Dⁱ-cong : ∀ {W X Y Z} → W ≈ₘ Y → X ≈ₘ Z → Dⁱ W X ≡ Dⁱ Y Z
    Dⁱ-cong W≈Y X≈Z = max⁺-cong (λ i j → dⁱ-cong (W≈Y i j) (X≈Z i j))

{-
    X≈Y⇒Dⁱ≡0 : ∀ {X Y} → X ≈ₘ Y → Dⁱ X Y ≡ 0
    X≈Y⇒Dⁱ≡0 {X} {Y} X≈Y = max⁺-constant (λ i j → x≈y⇒dⁱ≡0 (X≈Y i j))

    Dⁱ≡0⇒X≈Y : ∀ {X Y} → Dⁱ X Y ≡ 0 → X ≈ₘ Y
    Dⁱ≡0⇒X≈Y {X} {Y} DXY≡0 i j = dⁱ≡0⇒x≈y (≤-antisym (subst (dⁱ (X i j) (Y i j) ≤_) DXY≡0 (M≤max⁺[M] (zipWith dⁱ X Y) i j)) z≤n)

-}

    Dⁱ-sym : ∀ X Y → Dⁱ X Y ≡ Dⁱ Y X
    Dⁱ-sym X Y = max⁺-cong (zipWith-sym _≡_ dⁱ-sym X Y)


    Dⁱ-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ Dⁱ
    Dⁱ-maxTriIneq X Y Z = begin
      Dⁱ X Z                                                 ≡⟨ refl ⟩
      max⁺ (λ i j → dⁱ (X i j) (Z i j))                      ≤⟨ max⁺[M]≤max⁺[N] (λ i j → dⁱ-maxTriIneq (X i j) (Y i j) (Z i j)) ⟩
      max⁺ (λ i j → dⁱ (X i j) (Y i j) ⊔ dⁱ (Y i j) (Z i j)) ≡⟨ sym (max⁺[M]-distrib-⊔ (zipWith dⁱ X Y) (zipWith dⁱ Y Z)) ⟩
      Dⁱ X Y ⊔ Dⁱ Y Z ∎
      where open ≤-Reasoning
    
    

    XⁱYᶜ⇒DⁱXY≡DⁱX : ∀ {X Y} → 𝑰ₘ X → 𝑪ₘ Y → Dⁱ X Y ≡ max⁺ (map (invert ∘ hⁱ) X)
    XⁱYᶜ⇒DⁱXY≡DⁱX {X} {Y} Xⁱ Yᶜ with max⁺[M]∈M (zipWith dⁱ X Y) | 𝑰ₘ-witness Xⁱ
    ... | (i , j , max[M]≡dXᵢⱼYᵢⱼ) | (k , l , Xₖₗⁱ) = begin
      max⁺ (zipWith dⁱ X Y)      ≡⟨ {!!} ⟩
      max⁺ (map (invert ∘ hⁱ) X) ∎
      where open ≡-Reasoning
{-
    XⁱYᶜZᶜ⇒DⁱXZ≤DⁱXY : ∀ {X Y Z} → 𝑰ₘ X → 𝑪ₘ Y → 𝑪ₘ Z → Dⁱ X Z ≤ Dⁱ X Y
    XⁱYᶜZᶜ⇒DⁱXZ≤DⁱXY Xⁱ Yᶜ Zᶜ = ≤-reflexive (trans (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Zᶜ) (sym (XⁱYᶜ⇒DⁱXY≡DⁱX Xⁱ Yᶜ)))
    
    XᶜYᶜZⁱ⇒DⁱXZ≤DⁱYZ : ∀ {X Y Z} → 𝑪ₘ X → 𝑪ₘ Y → 𝑰ₘ Z → Dⁱ X Z ≤ Dⁱ Y Z
    XᶜYᶜZⁱ⇒DⁱXZ≤DⁱYZ Xᶜ Yᶜ Zⁱ = subst₂ _≤_ (Dⁱ-sym _ _) (Dⁱ-sym _ _) (XⁱYᶜZᶜ⇒DⁱXZ≤DⁱXY Zⁱ Yᶜ Xᶜ)


  ------------------------------------------------------------------------------
  -- Distance function
  ------------------------------------------------------------------------------
  -- A true distance function over IMatrices

  D : RMatrix → RMatrix → ℕ
  D X Y with X ≟ₘ Y | 𝑪ₘ? X | 𝑪ₘ? Y
  ... | yes _ | _      | _     = zero
  ... | no  _ | yes Xᶜ | yes Yᶜ = Dᶜ (toCMatrix Xᶜ) (toCMatrix Yᶜ)
  ... | no  _ | _      | _     = Hᶜ + Dⁱ X Y

{-
  D-cong : D Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
  D-cong {W} {X} {Y} {Z} W≈X Y≈Z with W ≟ₘ Y | X ≟ₘ Z 
  ... | yes _   | yes _   = refl
  ... | yes W≈Y | no  X≉Z = contradiction (≈ₘ-trans (≈ₘ-trans (≈ₘ-sym W≈X) W≈Y) Y≈Z) X≉Z
  ... | no  W≉Y | yes X≈Z = contradiction (≈ₘ-trans (≈ₘ-trans W≈X X≈Z) (≈ₘ-sym Y≈Z)) W≉Y
  ... | no _    | no _    with 𝑪ₘ? W | 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ...   | no  Wⁱ | yes Xᶜ | _      | _      = contradiction (𝑪ₘ-cong (≈ₘ-sym W≈X) Xᶜ) Wⁱ
  ...   | yes Wᶜ | no  Xⁱ | _      |  _     = contradiction (𝑪ₘ-cong W≈X Wᶜ) Xⁱ
  ...   | _      | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪ₘ-cong Y≈Z Yᶜ) Zⁱ
  ...   | _      | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪ₘ-cong (≈ₘ-sym Y≈Z) Zᶜ) Yⁱ
  ...   | no _   | no _   | _      | _      = cong (Hᶜ +_) (Dⁱ-cong W≈X Y≈Z)
  ...   | yes _  | yes _  | no  _  | no  _  = cong (Hᶜ +_) (Dⁱ-cong W≈X Y≈Z)
  ...   | yes _  | yes _  | yes _  | yes _  = Dᶜ-cong W≈X Y≈Z

  X≈Y⇒D≡0 : ∀ {X Y} → X ≈ₘ Y → D X Y ≡ 0
  X≈Y⇒D≡0 {X} {Y} X≈Y with X ≟ₘ Y
  ... | yes _   = refl
  ... | no  X≉Y = contradiction X≈Y X≉Y

  D≡0⇒X≈Y : ∀ {X Y} → D X Y ≡ 0 → X ≈ₘ Y
  D≡0⇒X≈Y {X} {Y} D≡0 with X ≟ₘ Y
  ... | yes X≈Y = X≈Y
  ... | no  _   with 𝑪ₘ? X | 𝑪ₘ? Y
  ...   | yes Xᶜ | yes Yᶜ = Dᶜ≡0⇒X≈Y D≡0
  ...   | no  Xⁱ | _     = contradiction D≡0 (m<n⇒n≢0 (≤-stepsʳ _ 1≤Hᶜ))
  ...   | yes Xᶜ | no  Yⁱ = contradiction D≡0 (m<n⇒n≢0 (≤-stepsʳ _ 1≤Hᶜ))
  
  D-sym : ∀ X Y → D X Y ≡ D Y X
  D-sym X Y with X ≟ₘ Y | Y ≟ₘ X
  ... | yes _   | yes _   = refl
  ... | yes X≈Y | no  Y≉X = contradiction (≈ₘ-sym X≈Y) Y≉X
  ... | no  X≉Y | yes Y≈X = contradiction (≈ₘ-sym Y≈X) X≉Y
  ... | no _    | no _    with 𝑪ₘ? X | 𝑪ₘ? Y
  ...   | yes _ | yes _ = Dᶜ-sym _ _
  ...   | no  _ | no  _ = cong (Hᶜ +_) (Dⁱ-sym X Y)
  ...   | no  _ | yes _ = cong (Hᶜ +_) (Dⁱ-sym X Y)
  ...   | yes _ | no  _ = cong (Hᶜ +_) (Dⁱ-sym X Y)
-}
  
  D-maxTriIneq-lemma : ∀ X Y Z → Hᶜ + Dⁱ X Z ≤ (Hᶜ + Dⁱ X Y) ⊔ (Hᶜ + Dⁱ Y Z)
  D-maxTriIneq-lemma X Y Z = begin
    Hᶜ + Dⁱ X Z                   ≤⟨ +-monoʳ-≤ Hᶜ (Dⁱ-maxTriIneq X Y Z) ⟩
    Hᶜ + (Dⁱ X Y ⊔ Dⁱ Y Z)        ≡⟨ +-distribˡ-⊔ Hᶜ _ _ ⟩
    (Hᶜ + Dⁱ X Y) ⊔ (Hᶜ + Dⁱ Y Z) ∎
    where open ≤-Reasoning

  --D-maxTriIneq-lemma₂ : ∀ X Y Z → X ≈ᶜₘ Y → Dᶜ X Z ≤ Dᶜ Y Z
  
  D-maxTriIneq : MaxTriangleIneq ℝ𝕄ₛ D
  D-maxTriIneq X Y Z with X ≟ₘ Z | X ≟ₘ Y | Y ≟ₘ Z
  D-maxTriIneq X Y Z | yes _   | _       | _       = z≤n
  D-maxTriIneq X Y Z | no  X≉Z | yes X≈Y | yes Y≈Z = contradiction (≈ₘ-trans X≈Y Y≈Z) X≉Z
  D-maxTriIneq X Y Z | no  _   | yes X≈Y | no  _   with 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ... | yes Xᶜ | yes Yᶜ | yes _ = ≤-reflexive (Dᶜ-cong (toCMatrix-cong Xᶜ Yᶜ X≈Y) ≈ₘ-refl)
  ... | yes Xᶜ | no  Yⁱ | _     = contradiction (𝑪ₘ-cong X≈Y Xᶜ) Yⁱ
  ... | no  Xⁱ | yes Yᶜ | _     = contradiction (𝑪ₘ-cong (≈ₘ-sym X≈Y) Yᶜ) Xⁱ
  ... | yes _  | yes _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong X≈Y ≈ₘ-refl))
  ... | no  _  | no  _  | yes _ = +-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong X≈Y ≈ₘ-refl))
  ... | no  _  | no  _  | no  _ = +-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong X≈Y ≈ₘ-refl))
  D-maxTriIneq X Y Z | no  _   | no  _   | yes Y≈Z with 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ... | yes _  | yes Yᶜ | yes Zᶜ = m≤n⇒m≤n⊔o 0 (≤-reflexive (Dᶜ-cong ≈ₘ-refl ((toCMatrix-cong Zᶜ Yᶜ (≈ₘ-sym Y≈Z)))))
  ... | _      | yes Yᶜ | no  Zⁱ = contradiction (𝑪ₘ-cong Y≈Z Yᶜ) Zⁱ
  ... | _      | no  Yⁱ | yes Zᶜ = contradiction (𝑪ₘ-cong (≈ₘ-sym Y≈Z) Zᶜ) Yⁱ
  ... | no  _  | yes _  | yes _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong ≈ₘ-refl (≈ₘ-sym Y≈Z))))
  ... | yes _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong ≈ₘ-refl (≈ₘ-sym Y≈Z))))
  ... | no  _  | no  _  | no  _  = m≤n⇒m≤n⊔o 0 (+-monoʳ-≤ Hᶜ (≤-reflexive (Dⁱ-cong ≈ₘ-refl (≈ₘ-sym Y≈Z))))
  D-maxTriIneq X Y Z | no  _   | no  _   | no  _   with 𝑪ₘ? X | 𝑪ₘ? Y | 𝑪ₘ? Z
  ... | yes _  | yes _  | yes _  = Dᶜ-maxTriIneq _ _ _
  ... | yes Xᶜ | yes Yᶜ | no  Zⁱ = m≤o⇒m≤n⊔o (Dᶜ _ _) (+-monoʳ-≤ Hᶜ (XᶜYᶜZⁱ⇒DⁱXZ≤DⁱYZ Xᶜ Yᶜ Zⁱ)) --()
  ... | no  Xⁱ | yes Yᶜ | yes Zᶜ = m≤n⇒m≤n⊔o {a = Hᶜ + Dⁱ X Y} (Dᶜ _ _) (+-monoʳ-≤ Hᶜ (XⁱYᶜZᶜ⇒DⁱXZ≤DⁱXY Xⁱ Yᶜ Zᶜ)) --()
  ... | yes Xᶜ | no  Yⁱ | yes Zᶜ = m≤n⇒m≤n⊔o (Hᶜ + Dⁱ Y Z) (≤-stepsʳ _ (Dᶜ≤Hᶜ _ _) )
  ... | yes _  | no  _  | no  _  = D-maxTriIneq-lemma X Y Z
  ... | no  _  | yes _  | no  _  = D-maxTriIneq-lemma X Y Z
  ... | no  _  | no  _  | yes _  = D-maxTriIneq-lemma X Y Z
  ... | no  _  | no  _  | no  _  = D-maxTriIneq-lemma X Y Z

{-

  
  
    }
    
{-
  d≡dᶜ : ∀ X Y → d (toIₘ X) (toIₘ Y) ≡ dᶜ X Y
  d≡dᶜ X Y with toIₘ X ≟ⁱₘ toIₘ Y
  ... | yes toX≈toY = ≡-sym (X≈Y⇒dᶜ≡0 (toIₘ-injective toX≈toY))
  ... | no  toX≉toY with 𝑪ₘ? (toIₘ X) | 𝑪ₘ? (toIₘ Y)
  ...   | no  toXⁱ | _        = contradiction (toIₘᶜ X) toXⁱ
  ...   | yes _   | no  toYⁱ = contradiction (toIₘᶜ Y) toYⁱ
  ...   | yes toXᶜ | yes toYᶜ  = dᶜ-cong (fromIₘ-toIₘ toXᶜ) (fromIₘ-toIₘ toYᶜ)
-}

-}
-}
