open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂) renaming (map to mapₚ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_; _≤_; _≤?_; _∸_; _⊔_; _⊓_; ≤-pred) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (m≤m+n; m+n∸m≡n; ≤+≢⇒<; suc-injective; ≤-trans; ≤-refl; ≤-total; ≤-reflexive; <-transʳ; <-transˡ; <-irrefl; ≤-antisym; ⊓-sel; ≰⇒≥; +-comm; +-assoc; +-mono-≤; ∸-mono; m≤m⊔n; ⊔-mono-≤; ⊔-comm; ⊔-sel; ⊓-mono-≤; m⊓n≤m; ⊓-idem; ⊓-assoc; ⊔-identityʳ; ⊓-comm; ⊔-mono-<; +-cancelˡ-≡; +-distribˡ-⊔; n≤m⊔n; +-monoʳ-<; <⇒≤; +-distribʳ-⊔; +-suc)
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
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m+o≡n; ∸-distribˡ-⊓-⊔; ⊔-monoˡ-≤; m≤n⇒m≤n⊔o; m≤o⇒m≤n⊔o; +-monoʳ-≤; ≤-stepsˡ; ∸-monoˡ-<; m≤n⇒m⊓n≡m; ∸-cancelʳ-≤; n<m⇒n⊓o<m; ⊔-triangulate; n≢0⇒0<n; ≤-stepsʳ; m>n⇒m∸n≢0; m<n⇒n≢0; ∸-monoˡ-≤; n≤m⇒n⊓o≤m; n≤m×o≤m⇒n⊔o≤m; n≤m⇒m⊔n≡m;  module ≤-Reasoning)
open import RoutingLib.Data.Matrix using (min⁺; map; max⁺; zipWith)
open import RoutingLib.Data.Matrix.Properties using (min⁺-cong; max⁺-constant; zipWith-sym; max⁺-cong; max⁺[M]≤max⁺[N]; M≤max⁺[M]; max⁺[M]-distrib-⊔; max⁺[M]≡x)
open import RoutingLib.Data.Matrix.Membership.Propositional.Properties using (max⁺[M]∈M)
open import RoutingLib.Function using (_∘₂_)
open import RoutingLib.Function.Distance using (Ultrametric; IsUltrametric; MaxTriangleIneq; Bounded)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.PathVector.Step1_InconsistentHeightFunction as Step1

module RoutingLib.Routing.BellmanFord.PathVector.Step2_InconsistentRouteMetric
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open Prelude 𝓟𝓢𝓒

  open Step1 𝓟𝓢𝓒 using
    ( hⁱ ; Hⁱ ; hⁱ-cong ; 1≤hⁱ; hⁱ≤Hⁱ ; hⁱ-decr ; h[s]≤h[rᶜ] )
 

  dᵣⁱ : Route → Route → ℕ
  dᵣⁱ x y with x ≟ y
  ... | yes _ = 0
  ... | no  _ = hⁱ x ⊔ hⁱ y

  dᵣⁱ-cong : dᵣⁱ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  dᵣⁱ-cong {x} {y} {u} {v} x≈y u≈v with x ≟ u | y ≟ v
  ... | yes _   | yes _   = refl
  ... | yes x≈u | no  y≉v = contradiction (≈-trans (≈-trans (≈-sym x≈y) x≈u) u≈v) y≉v
  ... | no  x≉u | yes y≈v = contradiction (≈-trans (≈-trans x≈y y≈v) (≈-sym u≈v)) x≉u
  ... | no  _   | no  _   = cong₂ _⊔_ (hⁱ-cong x≈y) (hⁱ-cong u≈v)
  
  dᵣⁱ-sym : ∀ x y → dᵣⁱ x y ≡ dᵣⁱ y x
  dᵣⁱ-sym x y with x ≟ y | y ≟ x
  ... | yes _   | yes _ = refl
  ... | yes x≈y | no  y≉x = contradiction (≈-sym x≈y) y≉x
  ... | no  x≉y | yes y≈x = contradiction (≈-sym y≈x) x≉y
  ... | no  _   | no  _   = ⊔-comm (hⁱ x) (hⁱ y)

  dᵣⁱ≡0⇒x≈y : ∀ {x y} → dᵣⁱ x y ≡ 0 → x ≈ y
  dᵣⁱ≡0⇒x≈y {x} {y} dᵣⁱ≡0 with x ≟ y
  ... | yes x≈y = x≈y
  ... | no  x≉y = contradiction dᵣⁱ≡0 (m<n⇒n≢0 (m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)))
  
  x≈y⇒dᵣⁱ≡0 : ∀ {x y} → x ≈ y → dᵣⁱ x y ≡ 0
  x≈y⇒dᵣⁱ≡0 {x} {y} x≈y with x ≟ y
  ... | yes _   = refl
  ... | no  x≉y = contradiction x≈y x≉y
  
  dᵣⁱ-maxTriIneq : MaxTriangleIneq S dᵣⁱ
  dᵣⁱ-maxTriIneq x y z with x ≟ z | x ≟ y | y ≟ z
  ... | yes _   | _       | _       = z≤n
  ... | no  x≉z | yes x≈y | yes y≈z = contradiction (≈-trans x≈y y≈z) x≉z
  ... | no  _   | yes x≈y | no  _   = ≤-reflexive (cong (_⊔ hⁱ z) (hⁱ-cong x≈y))
  ... | no  _   | no  _   | yes y≈z = ≤-reflexive (trans (cong (hⁱ x ⊔_) (sym (hⁱ-cong y≈z))) (sym (⊔-identityʳ _)))
  ... | no  _   | no  _   | no  _   = begin
    hⁱ x ⊔ hⁱ z                   ≤⟨ ⊔-monoˡ-≤ (hⁱ z) (m≤m⊔n (hⁱ x) (hⁱ y)) ⟩
    hⁱ x ⊔ hⁱ y ⊔ hⁱ z            ≡⟨ ⊔-triangulate (hⁱ x) (hⁱ y) (hⁱ z) ⟩
    (hⁱ x ⊔ hⁱ y) ⊔ (hⁱ y ⊔ hⁱ z) ∎
    where open ≤-Reasoning
  
  dᵣⁱ-isUltrametric : IsUltrametric S dᵣⁱ
  dᵣⁱ-isUltrametric = record
    { cong        = dᵣⁱ-cong
    ; eq⇒0        = x≈y⇒dᵣⁱ≡0
    ; 0⇒eq        = dᵣⁱ≡0⇒x≈y
    ; sym         = dᵣⁱ-sym
    ; maxTriangle = dᵣⁱ-maxTriIneq
    }
  
  dᵣⁱ-ultrametric : Ultrametric S
  dᵣⁱ-ultrametric = record
    { d             = dᵣⁱ
    ; isUltrametric = dᵣⁱ-isUltrametric
    }

  dᵣⁱ≤Hⁱ : ∀ x y → dᵣⁱ x y ≤ Hⁱ
  dᵣⁱ≤Hⁱ x y with x ≟ y
  ... | yes _ = z≤n
  ... | no  _ = n≤m×o≤m⇒n⊔o≤m (hⁱ≤Hⁱ x) (hⁱ≤Hⁱ y)
  
  dᵣⁱ-bounded : Bounded S dᵣⁱ
  dᵣⁱ-bounded = Hⁱ , dᵣⁱ≤Hⁱ



  h-force-𝑰 : ∀ {x y} → hⁱ x ≤ hⁱ y → 𝑰 x → 𝑰 y
  h-force-𝑰 {x} {y} hx≤hy xⁱ yᶜ = xⁱ (h[s]≤h[rᶜ] x yᶜ hx≤hy)
  
  dᵣⁱ-strContr-lemma : ∀ f {x y} → 𝑰 x → hⁱ (f ▷ y) ≤ hⁱ (f ▷ x) → hⁱ (f ▷ x) ⊔ hⁱ (f ▷ y) < hⁱ x ⊔ hⁱ y
  dᵣⁱ-strContr-lemma f {x} {y} xⁱ hfy≤hfx = begin
    hⁱ (f ▷ x) ⊔ hⁱ (f ▷ y)  ≡⟨ n≤m⇒m⊔n≡m hfy≤hfx ⟩
    hⁱ (f ▷ x)               <⟨ hⁱ-decr f xⁱ ⟩
    hⁱ x                     ≤⟨ m≤m⊔n (hⁱ x) (hⁱ y) ⟩
    hⁱ x       ⊔ hⁱ y        ∎
    where open ≤-Reasoning

  dᵣⁱ-strContr : ∀ f {x y} → x ≉ y → 𝑰 (f ▷ x) ⊎ 𝑰 (f ▷ y) → dᵣⁱ (f ▷ x) (f ▷ y) < dᵣⁱ x y
  dᵣⁱ-strContr f {x} {y} x≉y fxⁱ⊎fyⁱ with x ≟ y | f ▷ x ≟ f ▷ y
  ... | yes x≈y | _     = contradiction x≈y x≉y
  ... | no  _   | yes _ = m≤o⇒m≤n⊔o (hⁱ x) (1≤hⁱ y)
  ... | no  _   | no  _ with ≤-total (hⁱ (f ▷ x)) (hⁱ (f ▷ y))
  ...   | inj₂ hfy≤hfx = dᵣⁱ-strContr-lemma f (fxⁱ⇒xⁱ ([ id , h-force-𝑰 hfy≤hfx ]′ fxⁱ⊎fyⁱ)) hfy≤hfx
  ...   | inj₁ hfx≤hfy = begin
    hⁱ (f ▷ x) ⊔ hⁱ (f ▷ y) ≡⟨ ⊔-comm (hⁱ (f ▷ x)) (hⁱ (f ▷ y)) ⟩
    hⁱ (f ▷ y) ⊔ hⁱ (f ▷ x) <⟨ dᵣⁱ-strContr-lemma f (fxⁱ⇒xⁱ ([ h-force-𝑰 hfx≤hfy , id ]′ fxⁱ⊎fyⁱ)) hfx≤hfy ⟩
    hⁱ y       ⊔ hⁱ x       ≡⟨ ⊔-comm (hⁱ y) (hⁱ x) ⟩
    hⁱ x       ⊔ hⁱ y       ∎
    where open ≤-Reasoning
