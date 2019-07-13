
open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.FreeNetworks
  {a b ℓ n}
  {alg : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra alg)
  (A : AdjacencyMatrix alg n) where

open RawRoutingAlgebra alg
open IsRoutingAlgebra isRoutingAlgebra

open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Fin using (Fin; suc; inject≤; fromℕ; fromℕ≤; inject₁; 0F; 1F)
open import Data.List hiding ([_])
open import Data.List.Membership.Setoid S
open import Data.List.Properties
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (∃; ∃₂; _,_; proj₁; proj₂; _×_)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All as All
open import Data.Unit hiding (_≤_)
open import Function
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Level using (Level; _⊔_)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.Construct.Union as Union using (_∪_)
open import Relation.Binary.Construct.Closure.Transitive as TransClosure hiding ([_]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open import RoutingLib.Routing alg n
open import RoutingLib.Routing.Extensions alg A
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

-- open import RoutingLib.Data.Table hidin
open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties S
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Nullary using (Finite)
open import RoutingLib.Data.Maybe.Properties
import RoutingLib.Relation.Binary.Construct.Union as Union
import RoutingLib.Relation.Binary.Construct.TransitiveClosure as TransClosure
open import RoutingLib.Relation.Binary.Construct.TransitiveClosure using (steps; index)

open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

--------------------------------------------------------------------------------
-- Dominates relation
--------------------------------------------------------------------------------

_⊴_ : Rel Route ℓ
x ⊴ y = ∃₂ λ k j → A k j ▷ x ≤₊ y

postulate ⊴-respˡ-≈ : _⊴_ Respectsˡ _≈_

postulate ⊴-respʳ-≈ : _⊴_ Respectsʳ _≈_

⊴-≤₊-trans : Trans _⊴_ _≤₊_ _⊴_
⊴-≤₊-trans (k , j , Aₖⱼ▷x≤y) y≤z = k , j , ≤₊-trans Aₖⱼ▷x≤y y≤z

↝⇒⊴ : _↝_ ⇒ _⊴_
↝⇒⊴ (i , j , Aᵢⱼ▷x≈y) = i , j , ≤₊-reflexive Aᵢⱼ▷x≈y

--------------------------------------------------------------------------------
-- Cycle free networks
--------------------------------------------------------------------------------

Cyclic : FiniteSet⁺ Route →  Set ℓ
Cyclic ⟦ _ ∣ x ⟧ = ∀ i → x (i -ₘ 1) ⊴ x i
  
CycleFree : Set (a ⊔ ℓ)
CycleFree = ∀ X → ¬ Cyclic X

x⊴x⇒↺⟦x⟧ : ∀ {x} → x ⊴ x → Cyclic ⟦ x ⟧
x⊴x⇒↺⟦x⟧ {x} x⊴x 0F = x⊴x

↺-free⇒¬[x≈y∧x↝y] : CycleFree → ∀ {x y} → ¬ (y ≤₊ x × x ↝ y)
↺-free⇒¬[x≈y∧x↝y] cf {x} (y≤x , (i , j , Aᵢⱼ▷x≈y)) = cf ⟦ x ⟧ (x⊴x⇒↺⟦x⟧ (i , j , ≤₊-respˡ-≈ (≈-sym Aᵢⱼ▷x≈y) y≤x))
{-
↺-free⇒↝-irrefl : CycleFree → Irreflexive _≈_ _↝_
↺-free⇒↝-irrefl cf = {!!}
-}

--------------------------------------------------------------------------------
-- Order
--------------------------------------------------------------------------------

infix 4 _<ᶠ_

_<ᶠ_ : Rel Route (a ⊔ ℓ)
_<ᶠ_ = Plus′ (_<₊_ ∪ _↝_)

⟦_⟧↝ : ∀ {x y} (x<y : x <ᶠ y) → Maybe (FiniteSet⁺ Route)
⟦_⟧↝ {x} [ inj₁ x₁ ]     = nothing
⟦_⟧↝ {x} [ inj₂ y ]      = just ⟦ x ⟧
⟦_⟧↝ {x} (inj₁ x₁ ∷ x<y) = ⟦ x<y ⟧↝
⟦_⟧↝ {x} (inj₂ y  ∷ x<y) with ⟦ x<y ⟧↝
... | nothing = just ⟦ x ⟧
... | just t  = just (⟦ x ⟧∪ t)

¬⟦x<ᶠy⟧↝⇒x<y : ∀ {x y} (x<y : x <ᶠ y) → ¬ Is-just ⟦ x<y ⟧↝ → x <₊ y
¬⟦x<ᶠy⟧↝⇒x<y [ inj₁ x<y ]     _  = x<y
¬⟦x<ᶠy⟧↝⇒x<y [ inj₂ x<y ]     v  = contradiction (just tt) v
¬⟦x<ᶠy⟧↝⇒x<y (inj₁ x<y ∷ y<z) eq = <₊-trans x<y (¬⟦x<ᶠy⟧↝⇒x<y y<z eq)
¬⟦x<ᶠy⟧↝⇒x<y (inj₂ x<y ∷ y<z) eq with ⟦ y<z ⟧↝
... | nothing = contradiction (just tt) eq
... | just _  = contradiction (just tt) eq

x≤y⇒x≤⟦y<ᶠz⟧↝₀ : ∀ {x y z} → x ≤₊ y → (y<ᶠz : y <ᶠ z) → All (λ v → x ≤₊ first v) ⟦ y<ᶠz ⟧↝
x≤y⇒x≤⟦y<ᶠz⟧↝₀ x≤y [ inj₁ _ ]        = nothing
x≤y⇒x≤⟦y<ᶠz⟧↝₀ x≤y [ inj₂ _ ]        = just x≤y
x≤y⇒x≤⟦y<ᶠz⟧↝₀ x≤y (inj₁ y<z ∷ z<ᶠw) = x≤y⇒x≤⟦y<ᶠz⟧↝₀ (≤₊-trans x≤y (proj₁ y<z)) z<ᶠw
x≤y⇒x≤⟦y<ᶠz⟧↝₀ x≤y (inj₂ y↝z ∷ z<ᶠw) with ⟦ z<ᶠw ⟧↝
... | nothing = just x≤y
... | just _  = just x≤y

x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x : ∀ {x y z} → z ≤₊ x → (y<ᶠz : y <ᶠ z) → All (λ v → last v ⊴ x) ⟦ y<ᶠz ⟧↝
x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x [ inj₁ x<z ]      = nothing
x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x [ inj₂ x↝z ]      = just (⊴-≤₊-trans (↝⇒⊴ x↝z) z≤x)
x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x (inj₁ x<y ∷ y<ᶠz) = x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x y<ᶠz
x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x {x} z≤x (_∷_ {y = w} (inj₂ x↝w) w<ᶠy) with ⟦ w<ᶠy ⟧↝ | inspect ⟦_⟧↝ w<ᶠy
... | nothing | [ eq ] = just (⊴-≤₊-trans (↝⇒⊴ x↝w) (≤₊-trans (proj₁ (¬⟦x<ᶠy⟧↝⇒x<y w<ᶠy (subst (λ v → ¬ Is-just v) (sym eq) λ()))) z≤x)) 
... | just v  | [ eq ] = just (subst (λ v → last v ⊴ _) (to-witness-subst eq) (All-witness test (x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x w<ᶠy)))

  -- All-witness′ {P = λ v₁ → last v₁ ⊴ x} eq {!x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x z≤x w<ᶠy!} --
  where
  test : Is-just ⟦ w<ᶠy ⟧↝
  test = subst Is-just (sym eq) (just {x = v} tt)
  
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ : ∀ {x y} (x<ᶠy : x <ᶠ y) → All (λ v → (∀ i → iᵗʰ v (inject₁ i) ⊴ iᵗʰ v (suc i))) ⟦ x<ᶠy ⟧↝
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₁ _ ]         = nothing
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₂ _ ]         = just λ()
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ (inj₁ x<z ∷ z<ᶠy)  = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ {x} {y} (_∷_ {y = z} (inj₂ x↝z) z<ᶠy)  with ⟦ z<ᶠy ⟧↝ | inspect ⟦_⟧↝ z<ᶠy 
... | nothing | _      = just λ()
... | just v  | [ eq ] = just λ
  -- Please don't ask about this monstrosity. Horrible hacks around definitional equality of `to-witness`
  { 0F      → ⊴-≤₊-trans (↝⇒⊴ x↝z) (subst (λ q → z ≤₊ FiniteSet⁺.x q 0F) (to-witness-subst eq) (All-witness test (x≤y⇒x≤⟦y<ᶠz⟧↝₀ ≤₊-refl z<ᶠy)))
  ; (suc i) → subst (λ v → ∀ i → iᵗʰ v (inject₁ i) ⊴ iᵗʰ v (suc i)) (to-witness-subst eq) (All-witness test (⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy)) i
  }
  where
  test : Is-just ⟦ z<ᶠy ⟧↝
  test = subst Is-just (sym eq) (just {x = v} tt)

<ᶠ-respʳ-≈ : _<ᶠ_ Respectsʳ _≈_
<ᶠ-respʳ-≈ = TransClosure.R⁺-respʳ-≈ (Union.respʳ _<₊_ _↝_ <₊-respʳ-≈ ↝-respʳ-≈)

<ᶠ-trans : Transitive _<ᶠ_
<ᶠ-trans = TransClosure.trans

<ᶠ-irrefl : CycleFree → Irreflexive _≈_ _<ᶠ_
<ᶠ-irrefl cf x≈y x<ᶠy with IsJust? ⟦ x<ᶠy ⟧↝
... | no  ¬∣x<ᶠy∣↝ = <₊-irrefl x≈y (¬⟦x<ᶠy⟧↝⇒x<y x<ᶠy ¬∣x<ᶠy∣↝)
... | yes ∣x<ᶠy∣↝  = cf (to-witness ∣x<ᶠy∣↝) ∣x<ᶠy∣↝-cyclic
  where
  ⟦x<ᶠy⟧₋₁⊴x        = All-witness ∣x<ᶠy∣↝ (x≈y⇒⟦y<ᶠz⟧↝₋₁⊴x ≤₊-refl x<ᶠy)
  x≤⟦x<ᶠy⟧₀         = All-witness ∣x<ᶠy∣↝ (x≤y⇒x≤⟦y<ᶠz⟧↝₀ (≤₊-reflexive (≈-sym x≈y)) x<ᶠy)
  ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁ = All-witness ∣x<ᶠy∣↝ (⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ x<ᶠy)
  
  ∣x<ᶠy∣↝-cyclic : Cyclic (to-witness ∣x<ᶠy∣↝)
  ∣x<ᶠy∣↝-cyclic 0F      = ⊴-≤₊-trans ⟦x<ᶠy⟧₋₁⊴x x≤⟦x<ᶠy⟧₀
  ∣x<ᶠy∣↝-cyclic (suc i) = ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁ i

x<ᶠAᵢⱼ▷x : ∀ {x i j} → x <ᶠ A i j ▷ x
x<ᶠAᵢⱼ▷x = {!!}

--------------------------------------------------------------------------------
-- Finiteness
--------------------------------------------------------------------------------

module _ (finite : IsFinite alg) (cf : CycleFree) where

  infix 4 _<ᶠ?_
  
  _<ᶠ?_ : Decidable _<ᶠ_
  _<ᶠ?_ = TransClosure.R⁺? {!!} (Union.decidable _<₊?_ _↝?_)

  routes : List Route
  routes = proj₁ finite

  ∈-routes : ∀ x → x ∈ routes
  ∈-routes = proj₂ finite
  
  h : Route → ℕ
  h x = suc (length (filter (x <ᶠ?_) routes))
  
  h-resp-▷ : ∀ x i j → h (A i j ▷ x) < h x
  h-resp-▷ x i j = s≤s (length-mono-< ⊂-res)
    where
    Aᵢⱼ≮Aᵢⱼ▷x : ¬ (A i j ▷ x <ᶠ A i j ▷ x)
    Aᵢⱼ≮Aᵢⱼ▷x = <ᶠ-irrefl cf ≈-refl
    
    ⊂-res : filter (A i j ▷ x <ᶠ?_) routes ⊂ filter (x <ᶠ?_) routes
    ⊂-res = filter-⊂
              (A i j ▷ x <ᶠ?_) <ᶠ-respʳ-≈
              (x <ᶠ?_)         <ᶠ-respʳ-≈
              (<ᶠ-trans x<ᶠAᵢⱼ▷x) (∈-routes (A i j ▷ x)) (x<ᶠAᵢⱼ▷x , Aᵢⱼ≮Aᵢⱼ▷x)
    
  1≤h : ∀ x → 1 ≤ h x
  1≤h x = s≤s z≤n

  h≤H : ∀ x → h x ≤ h 0#
  h≤H x = s≤s {!!}
