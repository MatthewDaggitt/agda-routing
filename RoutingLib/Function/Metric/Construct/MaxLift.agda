open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; z≤n; suc; _⊔_)
open import Data.Nat.Properties using (≤-antisym; ⊔-mono-≤; ≤-refl)
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
open import RoutingLib.Function.Metric

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
  )

d : S → S → ℕ
d x y = max 0 (λ i → dᵢ i (x i) (y i))

dᵢ≤d : ∀ x y i → dᵢ i (x i) (y i) ≤ d x y
dᵢ≤d x y = t≤max[t] 0 (λ i → dᵢ i (x i) (y i))

sym : (∀ {i} → Symmetric (Setoid 𝕊 at i) (dᵢ i)) → Symmetric ≈-setoid d
sym dᵢ-sym x y = max-cong refl (λ i → dᵢ-sym (x i) (y i))

cong : (∀ {i} → (dᵢ i) Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
         d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
cong dᵢ-cong m≈n p≈q = max-cong refl (λ i → dᵢ-cong (m≈n i) (p≈q i))

d≡0⇒x≈y : (∀ {i} {xᵢ yᵢ : Sᵢ i} → dᵢ i xᵢ yᵢ ≡ 0 → xᵢ ≈ᵢ yᵢ) → ∀ {x y} → d x y ≡ 0 → x ≈ y
d≡0⇒x≈y dᵢ≡0⇒x≈y {x} {y} d≡0 i = dᵢ≡0⇒x≈y (≤-antisym (subst (dᵢ i (x i) (y i) ≤_) d≡0 (dᵢ≤d x y i)) z≤n)

x≈y⇒d≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ i xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → d x y ≡ 0
x≈y⇒d≡0 x≈y⇒dᵢ≡0 x≈y = max-constant refl (λ i → x≈y⇒dᵢ≡0 (x≈y i))

maxTriIneq : (∀ {i} → MaxTriangleIneq (Setoid 𝕊 at i) (dᵢ i)) →
             MaxTriangleIneq ≈-setoid d
maxTriIneq dᵢ-ineq x y z with max[t]∈t 0 λ i → dᵢ i (x i) (z i)
... | inj₁ dxz≡0 = subst (_≤ d x y ⊔ d y z) (P.sym dxz≡0) z≤n
... | inj₂ (j , dxz≡dⱼxⱼzⱼ) = begin
  d x z                           ≡⟨ dxz≡dⱼxⱼzⱼ ⟩
  dᵢ j (x j) (z j)                  ≤⟨ dᵢ-ineq _ _ _ ⟩
  dᵢ j (x j) (y j) ⊔ dᵢ j (y j) (z j) ≤⟨ ⊔-mono-≤ (dᵢ≤d x y j) (dᵢ≤d y z j) ⟩
  d x y ⊔ d y z                   ∎
  where open ≤-Reasoning

bounded : (∀ {i} → Bounded (Setoid 𝕊 at i) (dᵢ i)) → Bounded ≈-setoid d
bounded dᵢ-bounded =
    (max 0 (λ i → proj₁ (dᵢ-bounded {i}))) ,
    (λ x y → max[s]≤max[t]₂ (≤-refl {0}) (λ i → proj₂ (dᵢ-bounded {i}) (x i) (y i)))

isUltrametric : (∀ {i} → IsUltrametric (Setoid 𝕊 at i) (dᵢ i)) → IsUltrametric ≈-setoid d
isUltrametric um = record
  { cong        = cong     IsU.cong
  ; eq⇒0        = x≈y⇒d≡0    IsU.eq⇒0
  ; 0⇒eq        = d≡0⇒x≈y    IsU.0⇒eq
  ; sym         = sym      IsU.sym
  ; maxTriangle = maxTriIneq IsU.maxTriangle
  }
  where module IsU {i} = IsUltrametric (um {i})

{-
ultrametric : (∀ i → Ultrametric (Setoid 𝕊 at i)) → Ultrametric ≈-setoid
ultrametric um = record
  { d             = d (λ {i} → Ultrametric.d (um i))
  ; isUltrametric = isUltrametric (λ {i} → Ultrametric.isUltrametric (um i))
  }
-}
