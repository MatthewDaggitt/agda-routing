
import Algebra.FunctionProperties as AlgebraicProperties
open import Data.Fin as Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈; ∈-map⁺)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_on_)
open import Level using (_⊔_) renaming (zero to 0ℓ)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality using (inspect; [_]; _≡_; _≢_; refl; sym)
import Relation.Binary.On as On
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Unary as U hiding (Decidable; U)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Nullary.Decidable using (toSum)

open import RoutingLib.Data.Path.CertifiedI
open import RoutingLib.Data.Path.CertifiedI.Enumeration
open import RoutingLib.Data.Path.CertifiedI.Properties

open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.RoutingAlgebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties
  as PathAlgebraProperties

module RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency
  {a b ℓ n} (algebra : RawRoutingAlgebra a b ℓ)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open PathAlgebraProperties isPathAlgebra

--------------------------------------------------------------------------------
-- Consistency

weight-cong : ∀ {p q : Path n} → p ≈ₚ q → weight A p ≈ weight A q
weight-cong invalid              = ≈-refl
weight-cong (valid [])           = ≈-refl
weight-cong (valid (refl ∷ p≈q)) = ▷-cong _ (weight-cong (valid p≈q))

𝑪 : Route → Set ℓ
𝑪 r = weight A (path r) ≈ r

𝑰 : Route → Set ℓ
𝑰 r = ¬ 𝑪 r

𝑪? : U.Decidable 𝑪
𝑪? r = weight A (path r) ≟ r

𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
𝑪-cong r≈s rᶜ = ≈-trans (≈-trans (weight-cong (path-cong (≈-sym r≈s))) rᶜ) r≈s

𝑰-cong : ∀ {r s} → r ≈ s → 𝑰 r → 𝑰 s
𝑰-cong r≈s rⁱ sᶜ = rⁱ (𝑪-cong (≈-sym r≈s) sᶜ)

𝑪𝑰⇒≉ : ∀ {r s} → 𝑪 r → 𝑰 s → r ≉ s
𝑪𝑰⇒≉ rᶜ sⁱ r≈s = sⁱ (𝑪-cong r≈s rᶜ)

0ᶜ : 𝑪 0#
0ᶜ = weight-cong p[0]≈[]

∞ᶜ : 𝑪 ∞
∞ᶜ = weight-cong p[∞]≈∅

⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

▷-pres-𝑪 : ∀ i j {r} → 𝑪 r → 𝑪 (A i j ▷ r)
▷-pres-𝑪 i j {r} rᶜ with A i j ▷ r ≟ ∞
... | yes Aᵢⱼ▷r≈∞ = 𝑪-cong (≈-sym Aᵢⱼ▷r≈∞) ∞ᶜ
... | no  Aᵢⱼ▷r≉∞ with path r | inspect path r
...   | invalid | [ pᵣ≡∅ ] = contradiction (p[r]≡∅⇒f▷r≈∞ (A i j) pᵣ≡∅) Aᵢⱼ▷r≉∞
...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿ᵥ? q | i ∉ᵥₚ? q
...     | pᵣ≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject (A i j) pᵣ≈q (inj₁ ¬ij⇿q))) ∞ᶜ -- pᵣ≈q
...     | pᵣ≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject (A i j) pᵣ≈q (inj₂ i∈q))) ∞ᶜ -- pᵣ≈q
...     | pᵣ≈q | yes ij⇿q | yes i∉q = begin
  weight A (path (A i j ▷ r))                   ≈⟨ weight-cong {path (A i j ▷ r)} (path-accept (A i j) pᵣ≈q Aᵢⱼ▷r≉∞ ij⇿q i∉q) ⟩
  weight A (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q))   ≡⟨⟩
  A i j ▷ weight A (valid q)                    ≈⟨ ▷-cong (A i j) rᶜ ⟩
  A i j ▷ r                                     ∎
  where open EqReasoning S
  
▷-forces-𝑰 : ∀ {i j r} → 𝑰 (A i j ▷ r) → 𝑰 r
▷-forces-𝑰 f▷rⁱ rᶜ = f▷rⁱ (▷-pres-𝑪 _ _ rᶜ)

weightᶜ : ∀ p → 𝑪 (weight A p)
weightᶜ invalid                            = ∞ᶜ
weightᶜ (valid [])                         = 0ᶜ
weightᶜ (valid ((i , j) ∷ p ∣ e⇿p ∣ e∉p)) with A i j ▷ weight A (valid p) ≟ ∞
... | yes Aᵢⱼ▷wₚ≈∞ = 𝑪-cong (≈-sym Aᵢⱼ▷wₚ≈∞) ∞ᶜ
... | no  Aᵢⱼ▷wₚ≉∞ with path (weight A (valid p)) | inspect path (weight A (valid p))
...   | invalid | [ p[wₚ]≡∅ ] = 𝑪-cong (≈-sym (p[r]≡∅⇒f▷r≈∞ (A i j) p[wₚ]≡∅)) ∞ᶜ
...   | valid q | [ p[wₚ]≡q ] with ≈ₚ-reflexive p[wₚ]≡q | (i , j) ⇿ᵥ? q | i ∉ᵥₚ? q
...     | p[wₚ]≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject (A i j) p[wₚ]≈q (inj₁ ¬ij⇿q))) ∞ᶜ
...     | p[wₚ]≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject (A i j) p[wₚ]≈q (inj₂ i∈q))) ∞ᶜ
...     | p[wₚ]≈q | yes ij⇿q | yes i∉q = begin
  weight A (path (A i j ▷ weight A (valid p)))  ≈⟨ weight-cong (path-accept (A i j) p[wₚ]≈q Aᵢⱼ▷wₚ≉∞ ij⇿q i∉q) ⟩
  weight A (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q))   ≡⟨⟩
  A i j ▷ weight A (valid q)                    ≈⟨ ▷-cong (A i j) (weight-cong (≈ₚ-sym p[wₚ]≈q)) ⟩
  A i j ▷ weight A (path (weight A (valid p)))  ≈⟨ ▷-cong (A i j) (weightᶜ (valid p)) ⟩
  A i j ▷ weight A (valid p)                    ∎
  where open EqReasoning S

sizeⁱ-incr : ∀ {i j : Fin n} {r} {f : Step i j} → 𝑰 (f ▷ r) → suc (size r) ≡ size (f ▷ r)
sizeⁱ-incr {i} {j} {r} {f} f▷rⁱ with f ▷ r ≟ ∞
... | yes f▷r≈∞ = contradiction (𝑪-cong (≈-sym f▷r≈∞) ∞ᶜ) f▷rⁱ
... | no  f▷r≉∞ with path r | inspect path r
...   | invalid | [ pᵣ≡∅ ] = contradiction (p[r]≡∅⇒f▷r≈∞ f pᵣ≡∅) f▷r≉∞
...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿ᵥ? q | i ∉ᵥₚ? q
...     | pᵣ≈q | no ¬ij⇿q | _       = contradiction (path-reject f pᵣ≈q (inj₁ ¬ij⇿q)) f▷r≉∞
...     | pᵣ≈q | _        | no  i∈q = contradiction (path-reject f pᵣ≈q (inj₂ i∈q)) f▷r≉∞
...     | pᵣ≈q | yes ij⇿q | yes i∉q = sym (length-cong (path-accept f pᵣ≈q f▷r≉∞ ij⇿q i∉q))

------------------------------------------------------------------------------
-- Types

CRoute : Set _
CRoute = Σ Route 𝑪

-- Note: U i j is never used but is included so that i and j are inferrable
CStep : ∀ {m} → Fin m → Fin m → Set
CStep i j = Maybe (Fin n × Fin n) × (i ≡ j ⊎ i ≢ j)

------------------------------------------------------------------------------
-- Special routes

C0# : CRoute
C0# = 0# , 0ᶜ

C∞ : CRoute
C∞ = ∞ , ∞ᶜ

------------------------------------------------------------------------------
-- Equality

infix 4 _≈ᶜ_ _≉ᶜ_ _≟ᶜ_

_≈ᶜ_ : Rel CRoute _
_≈ᶜ_ = _≈_ on proj₁

_≉ᶜ_ : Rel CRoute _
r ≉ᶜ s = ¬ (r ≈ᶜ s)

_≟ᶜ_ : B.Decidable _≈ᶜ_
_ ≟ᶜ _ = _ ≟ _

≈ᶜ-isDecEquivalence : IsDecEquivalence _≈ᶜ_
≈ᶜ-isDecEquivalence = On.isDecEquivalence proj₁ ≈-isDecEquivalence

Sᶜ : Setoid _ _
Sᶜ = On.setoid {B = CRoute} S proj₁

DSᶜ : DecSetoid _ _
DSᶜ = On.decSetoid {B = CRoute} DS proj₁

------------------------------------------------------------------------------
-- Choice operator

open AlgebraicProperties _≈ᶜ_

infix 7 _⊕ᶜ_

_⊕ᶜ_ : Op₂ CRoute
(r , rᶜ) ⊕ᶜ (s , sᶜ) = r ⊕ s , ⊕-pres-𝑪 rᶜ sᶜ

⊕ᶜ-cong : Congruent₂ _⊕ᶜ_
⊕ᶜ-cong = ⊕-cong

------------------------------------------------------------------------------
-- Extension functions

infix 6 _▷ᶜ_

_▷ᶜ_ : ∀{n} {i j : Fin n} → CStep i j → CRoute → CRoute
(nothing       , _) ▷ᶜ (r , rᶜ) = C∞
(valid (k , l) , _) ▷ᶜ (r , rᶜ) = A k l ▷ r , ▷-pres-𝑪 k l rᶜ

▷ᶜ-cong : ∀ {n} {i j : Fin n} (f : CStep i j) {r s} → r ≈ᶜ s → f ▷ᶜ r ≈ᶜ f ▷ᶜ s
▷ᶜ-cong (nothing       , _) = λ _ → ≈-refl
▷ᶜ-cong (valid (k , l) , _) = ▷-cong (A k l)

f∞ᶜ : ∀ {n} (i j : Fin n) → CStep i j
f∞ᶜ i j = nothing , toSum (i Fin.≟ j)

f∞ᶜ-reject : ∀ {n} (i j : Fin n) → ∀ x → (f∞ᶜ i j) ▷ᶜ x ≈ᶜ C∞
f∞ᶜ-reject _ _ _ = ≈-refl

------------------------------------------------------------------------------
-- Raw routing algebra

algebraᶜ : RawRoutingAlgebra 0ℓ (b ⊔ ℓ) ℓ
algebraᶜ = record
  { Step               = CStep
  ; Route              = CRoute
  ; _≈_                = _≈ᶜ_
  ; _⊕_                = _⊕ᶜ_
  ; _▷_                = _▷ᶜ_
  ; 0#                 = C0#
  ; ∞                  = C∞
  ; f∞                 = f∞ᶜ
  ; ≈-isDecEquivalence = ≈ᶜ-isDecEquivalence
  ; ⊕-cong             = ⊕-cong
  ; ▷-cong             = ▷ᶜ-cong
  ; f∞-reject          = f∞ᶜ-reject
  }

------------------------------------------------------------------------------
-- Routing algebra properties

⊕ᶜ-assoc : Associative _⊕ᶜ_
⊕ᶜ-assoc _ _ _ = ⊕-assoc _ _ _

⊕ᶜ-comm : Commutative _⊕ᶜ_
⊕ᶜ-comm _ _ = ⊕-comm _ _

⊕ᶜ-sel : Selective _⊕ᶜ_
⊕ᶜ-sel _ _ = ⊕-sel _ _

⊕ᶜ-zeroʳ : RightZero C0# _⊕ᶜ_
⊕ᶜ-zeroʳ _ = ⊕-zeroʳ _

⊕ᶜ-identityʳ : RightIdentity C∞ _⊕ᶜ_
⊕ᶜ-identityʳ _ = ⊕-identityʳ _

▷ᶜ-fixedPoint : ∀ {n} {i j : Fin n} (f : CStep i j) → f ▷ᶜ C∞ ≈ᶜ C∞
▷ᶜ-fixedPoint (nothing       , _) = ≈-refl 
▷ᶜ-fixedPoint (valid (k , l) , _) = ▷-fixedPoint (A k l)

isRoutingAlgebraᶜ : IsRoutingAlgebra algebraᶜ
isRoutingAlgebraᶜ = record
  { ⊕-sel        = ⊕ᶜ-sel
  ; ⊕-comm       = ⊕ᶜ-comm
  ; ⊕-assoc      = ⊕ᶜ-assoc
  ; ⊕-zeroʳ      = ⊕ᶜ-zeroʳ
  ; ⊕-identityʳ  = ⊕ᶜ-identityʳ
  ; ▷-fixedPoint = ▷ᶜ-fixedPoint
  }

------------------------------------------------------------------------------
-- Optional properties

isIncreasingᶜ : IsIncreasing algebra → IsIncreasing algebraᶜ
isIncreasingᶜ incr (valid (k , l) , _) (r , _) = incr (A k l) r
isIncreasingᶜ incr (nothing       , _) (r , _) = ⊕-identityˡ r

isStrictlyIncreasingᶜ : IsStrictlyIncreasing algebra → IsStrictlyIncreasing algebraᶜ
isStrictlyIncreasingᶜ sIncr (valid (k , l) , _)     = sIncr (A k l)
isStrictlyIncreasingᶜ sIncr (nothing       , _) r≉∞ = (⊕-identityˡ _) , r≉∞

isFiniteᶜ : IsFinite algebraᶜ
isFiniteᶜ = allCRoutes , ∈-allCRoutes
  where
  open Membership Sᶜ using () renaming (_∈_ to _∈ₗ_)

  pathToCRoute : Path n → CRoute
  pathToCRoute p = weight A p , weightᶜ p

  abstract

    allCRoutes : List CRoute
    allCRoutes = map pathToCRoute (allPaths n)

    ∈-allCRoutes : ∀ r → r ∈ₗ allCRoutes
    ∈-allCRoutes (r , rᶜ) = ∈-resp-≈ Sᶜ {x = pathToCRoute (path r)} {r , rᶜ}
      rᶜ (∈-map⁺ (ℙₛ n) Sᶜ weight-cong (∈-allPaths (path r)))

------------------------------------------------------------------------------
-- Conversion

toCRoute : ∀ {r} → 𝑪 r → CRoute
toCRoute {r} rᶜ = r , rᶜ

fromCRoute : CRoute → Route
fromCRoute (r , _ ) = r

------------------------------------------------------------------------------
-- Adjacency matrix

Aᶜ : AdjacencyMatrix algebraᶜ n
Aᶜ i j = just (i , j) , toSum (i Fin.≟ j)
