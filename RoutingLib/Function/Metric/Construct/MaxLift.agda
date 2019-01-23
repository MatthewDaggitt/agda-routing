open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; z≤n; suc; _⊔_)
open import Data.Nat.Properties using (≤-antisym; ⊔-mono-≤; ≤-refl; ≤-isTotalOrder)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)

open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (max-cong; t≤max[t]; max-constant; max[s]≤max[t]₂)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid_at_)
open import RoutingLib.Function.Metric.Nat

module RoutingLib.Function.Metric.Construct.MaxLift
  {a ℓ n} (𝕊 : IndexedSetoid (Fin n) a ℓ)
  (dᵢ : ∀ i → IndexedSetoid.Carrierᵢ 𝕊 i → IndexedSetoid.Carrierᵢ 𝕊 i → ℕ)
  where

open IndexedSetoid 𝕊
  using (_≈_; _≈ᵢ_)
  renaming
  ( Carrier  to S
  ; Carrierᵢ to Sᵢ
  ; setoid   to ≈-setoid
  ; isEquivalence to ≈-isEquivalence
  )

d : S → S → ℕ
d x y = max 0 (λ i → dᵢ i (x i) (y i))

dᵢ≤d : ∀ x y i → dᵢ i (x i) (y i) ≤ d x y
dᵢ≤d x y = t≤max[t] 0 (λ i → dᵢ i (x i) (y i))

sym : (∀ {i} → Symmetric (dᵢ i)) → Symmetric d
sym dᵢ-sym x y = max-cong refl (λ i → dᵢ-sym (x i) (y i))

cong : (∀ {i} → (dᵢ i) Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
       d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
cong dᵢ-cong m≈n p≈q = max-cong refl (λ i → dᵢ-cong (m≈n i) (p≈q i))

d≡0⇒dᵢ≡0 : ∀ {x y} → d x y ≡ 0 → ∀ i → dᵢ i (x i) (y i) ≡ 0
d≡0⇒dᵢ≡0 d≡0 i = ≤-antisym (subst (_ ≤_) d≡0 (dᵢ≤d _ _ i)) z≤n

d≡0⇒x≈y : (∀ {i} {xᵢ yᵢ : Sᵢ i} → dᵢ i xᵢ yᵢ ≡ 0 → xᵢ ≈ᵢ yᵢ) → ∀ {x y} → d x y ≡ 0 → x ≈ y
d≡0⇒x≈y dᵢ≡0⇒x≈y {x} {y} d≡0 i = dᵢ≡0⇒x≈y (d≡0⇒dᵢ≡0 d≡0 i)

x≈y⇒d≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ i xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → d x y ≡ 0
x≈y⇒d≡0 x≈y⇒dᵢ≡0 x≈y = max-constant refl (λ i → x≈y⇒dᵢ≡0 (x≈y i))

maxTriIneq : (∀ {i} → MaxTriangleInequality (dᵢ i)) → MaxTriangleInequality d
maxTriIneq dᵢ-ineq x y z with max[t]∈t 0 λ i → dᵢ i (x i) (z i)
... | inj₁ dxz≡0 = subst (_≤ d x y ⊔ d y z) (P.sym dxz≡0) z≤n
... | inj₂ (j , dxz≡dⱼxⱼzⱼ) = begin
  d x z                           ≡⟨ dxz≡dⱼxⱼzⱼ ⟩
  dᵢ j (x j) (z j)                  ≤⟨ dᵢ-ineq _ _ _ ⟩
  dᵢ j (x j) (y j) ⊔ dᵢ j (y j) (z j) ≤⟨ ⊔-mono-≤ (dᵢ≤d x y j) (dᵢ≤d y z j) ⟩
  d x y ⊔ d y z                   ∎
  where open ≤-Reasoning

bounded : (∀ {i} → Bounded (dᵢ i)) → Bounded d
bounded dᵢ-bounded =
    (max 0 (λ i → proj₁ (dᵢ-bounded {i}))) ,
    (λ x y → max[s]≤max[t]₂ (≤-refl {0}) (λ i → proj₂ (dᵢ-bounded {i}) (x i) (y i)))

isPreMetric : (∀ {i} → IsPreMetric _≈ᵢ_ (dᵢ i)) → IsPreMetric _≈_ d
isPreMetric pm = record
  { isTotalOrder    = ≤-isTotalOrder
  ; 0#-minimum      = z≤n
  ; ≈-isEquivalence = ≈-isEquivalence
  ; cong            = cong (IsPreMetric.cong pm)
  ; eq⇒0            = x≈y⇒d≡0 (IsPreMetric.eq⇒0 pm)
  }

isQuasiSemiMetric : (∀ {i} → IsQuasiSemiMetric _≈ᵢ_ (dᵢ i)) → IsQuasiSemiMetric _≈_ d
isQuasiSemiMetric qsm = record
  { isPreMetric = isPreMetric (IsQuasiSemiMetric.isPreMetric qsm)
  ; 0⇒eq        = d≡0⇒x≈y (IsQuasiSemiMetric.0⇒eq qsm)
  }

isSemiMetric : (∀ {i} → IsSemiMetric _≈ᵢ_ (dᵢ i)) → IsSemiMetric _≈_ d
isSemiMetric sm = record
  { isQuasiSemiMetric = isQuasiSemiMetric (IsSemiMetric.isQuasiSemiMetric sm)
  ; sym               = sym (IsSemiMetric.sym sm)
  }

isUltraMetric : (∀ {i} → IsUltraMetric _≈ᵢ_ (dᵢ i)) → IsUltraMetric _≈_ d
isUltraMetric um = record
  { isSemiMetric = isSemiMetric (IsUltraMetric.isSemiMetric um)
  ; triangle     = maxTriIneq (IsUltraMetric.triangle um)
  }

{-
ultrametric : (∀ i → UltraMetric a ℓ) → UltraMetric {!!} {!!}
ultrametric um = record
  { d             = {!!} --d (λ {i} → UltraMetric.d (um i))
  ; isUltraMetric = isUltraMetric {!!} --(λ {i} → UltraMetric.isUltraMetric (um i))
  }
-}
