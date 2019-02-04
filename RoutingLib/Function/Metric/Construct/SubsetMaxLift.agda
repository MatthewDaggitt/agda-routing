open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; _≤_; z≤n; suc; _⊔_)
open import Data.Nat.Properties using (≤-reflexive; ≤-antisym; ⊔-mono-≤; ≤-refl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Binary.Indexed.Homogeneous using (IndexedSetoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (max-cong; x≤max[t]; max-constant; max[s]≤max[t]₂)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous using (Setoid_at_)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.Equality as SubsetEquality
open import RoutingLib.Function.Metric
import RoutingLib.Function.Metric.Construct.MaxLift as MaxLift

module RoutingLib.Function.Metric.Construct.SubsetMaxLift {a ℓ n} (𝕊 : IndexedSetoid (Fin n) a ℓ) where

open IndexedSetoid 𝕊
  using (_≈_; _≈ᵢ_)
  renaming
  ( Carrier  to S
  ; Carrierᵢ to Sᵢ
  ; setoid   to ≈-setoid
  )

open SubsetEquality 𝕊 using (_≈[_]_; ≈⇒≈ₛ)
open MaxLift 𝕊 using (d)

module _ (dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ) (p : Subset n) where


{-

  dˢ : S → S → ℕ
  dˢ x y = max 0 (λ i → cond (x i) (y i))

  x≈y⇒dˢ≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → dˢ x y ≡ 0
  x≈y⇒dˢ≡0 eq x≈y = max-constant refl (λ i → x≈y⇒cond≡0 eq (x≈y i))

  dˢ≡0⇒x≈ₛy : (∀ {i} {x y : Sᵢ i} → dᵢ x y ≡ 0 → x ≈ᵢ y) → ∀ {x y} → dˢ x y ≡ 0 → x ≈[ p ] y
  {-dˢ≡0⇒x≈ₛy {x} {y} dˢ≡0 {i} i∈p with i ∈? p
  ... | yes _   = {!!}
  ... | no  i∉p = {!contradiction !}
  -}

  dᵢ≤dˢ : ∀ x y {i} → i ∈ p → dᵢ (x i) (y i) ≤ dˢ x y
  dᵢ≤dˢ x y {i} i∈p = x≤max[t] 0 _ (inj₂ (i , ≤-reflexive (sym (cond-eq (x i) (y i) i∈p))))

  dˢ-sym : (∀ {i} → Symmetric (Setoid 𝕊 at i) (dᵢ {i})) → Symmetric ≈-setoid dˢ
  dˢ-sym dᵢ-sym x y = max-cong refl (λ i → cond-sym dᵢ-sym (x i) (y i))

  dˢ-congˢ : (∀ {i} → dᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
             dˢ Preserves₂ _≈[ p ]_ ⟶ _≈[ p ]_ ⟶ _≡_
  dˢ-congˢ dᵢ-cong m≈n p≈q = max-cong refl (λ i → cond-cong dᵢ-cong i m≈n p≈q)

  dˢ-cong : (∀ {i} → dᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
           dˢ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  dˢ-cong dᵢ-cong m≈n p≈q = dˢ-congˢ dᵢ-cong (≈⇒≈ₛ m≈n) (≈⇒≈ₛ p≈q)


  -- Relation to normal max lift

  dˢ≤d : ∀ x y → dˢ x y ≤ d dᵢ x y
  dˢ≤d x y = max[s]≤max[t]₂ z≤n (λ i → cond-leq (x i) (y i))

  dˢ≡d : ∀ x y → (∀ {i} → i ∉ p → dᵢ (x i) (y i) ≡ 0) → dˢ x y ≡ d dᵢ x y
  dˢ≡d x y eq = max-cong refl (λ i → cond-eq' i eq)
{-
    d≡0⇒x≈y : (∀ {i} {xᵢ yᵢ : Sᵢ i} → dᵢ xᵢ yᵢ ≡ 0 → xᵢ ≈ᵢ yᵢ) → ∀ {x y} → d x y ≡ 0 → x ≈ y
    d≡0⇒x≈y dᵢ≡0⇒x≈y {x} {y} d≡0 i = dᵢ≡0⇒x≈y (≤-antisym (subst (dᵢ (x i) (y i) ≤_) d≡0 (dᵢ≤d x y i)) z≤n)

    x≈y⇒d≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → d x y ≡ 0
    x≈y⇒d≡0 x≈y⇒dᵢ≡0 x≈y = max-constant refl (λ i → x≈y⇒dᵢ≡0 (x≈y i))



    maxTriIneq : (∀ {i} → MaxTriangleIneq (Setoid 𝕊 at i) dᵢ) →
                 MaxTriangleIneq ≈-setoid d
    maxTriIneq dᵢ-ineq x y z with max[t]∈t 0 λ i → dᵢ (x i) (z i)
    ... | inj₁ dxz≡0 = subst (_≤ d x y ⊔ d y z) (sym dxz≡0) z≤n
    ... | inj₂ (j , dxz≡dⱼxⱼzⱼ) = begin
      d x z                           ≡⟨ dxz≡dⱼxⱼzⱼ ⟩
      dᵢ (x j) (z j)                   ≤⟨ dᵢ-ineq _ _ _ ⟩
      dᵢ (x j) (y j) ⊔ dᵢ (y j) (z j)  ≤⟨ ⊔-mono-≤ (dᵢ≤d x y j) (dᵢ≤d y z j) ⟩
      d x y ⊔ d y z                   ∎
      where open ≤-Reasoning

bounded : {dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ} →
          (∀ {i} → Bounded (Setoid 𝕊 at i) dᵢ) → Bounded ≈-setoid (d dᵢ)
bounded dᵢ-bounded =
    (max 0 (λ i → proj₁ (dᵢ-bounded {i}))) ,
    (λ x y → max[s]≤max[t]₂ (≤-refl {0}) (λ i → proj₂ (dᵢ-bounded {i}) (x i) (y i)))

isUltrametric : {dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ} → (∀ {i} → IsUltrametric (Setoid 𝕊 at i) dᵢ) →
                IsUltrametric ≈-setoid (d dᵢ)
isUltrametric {dᵢ} um = record
  { cong        = d-cong    dᵢ λ {i} → IsUltrametric.cong (um {i})
  ; eq⇒0        = x≈y⇒d≡0   dᵢ λ {i} → IsUltrametric.eq⇒0 (um {i})
  ; 0⇒eq        = d≡0⇒x≈y   dᵢ (λ {i} → IsUltrametric.0⇒eq (um {i}))
  ; sym         = d-sym      dᵢ λ {i} → IsUltrametric.sym (um {i})
  ; maxTriangle = maxTriIneq dᵢ λ {i} → IsUltrametric.maxTriangle (um {i})
  }

ultrametric : (∀ i → Ultrametric (Setoid 𝕊 at i)) → Ultrametric ≈-setoid
ultrametric um = record
  { d             = d (λ {i} → Ultrametric.d (um i))
  ; isUltrametric = isUltrametric (λ {i} → Ultrametric.isUltrametric (um i))
  }
-}
-}
