open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; z≤n; suc; _⊔_)
open import Data.Nat.Properties using (≤-antisym; ⊔-mono-≤; ≤-refl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (max-cong; t≤max[t]; max-constant; max[s]≤max[t]₂)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
import RoutingLib.Data.Table.IndexedTypes as IndexedType
open import RoutingLib.Function.Metric

module RoutingLib.Function.Metric.MaxLift {a ℓ n} (𝕊ᵢ : Fin n → Setoid a ℓ) where

  open IndexedType 𝕊ᵢ using (S; 𝕊; _≈_)

  module _ (i : Fin n) where

    open Setoid (𝕊ᵢ i) using () renaming (Carrier to Sᵢ) public

  module _ {i : Fin n} where
    open Setoid (𝕊ᵢ i) using () renaming (_≈_ to _≈ᵢ_) public

  module _ (dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ) where
  
    d : S → S → ℕ
    d x y = max 0 (λ i → dᵢ (x i) (y i))

    abstract
  
      dᵢ≤d : ∀ x y i → dᵢ (x i) (y i) ≤ d x y
      dᵢ≤d x y = t≤max[t] 0 (λ i → dᵢ (x i) (y i))
    
      d-sym : (∀ {i} → Symmetric (𝕊ᵢ i) (dᵢ {i})) → Symmetric 𝕊 d
      d-sym dᵢ-sym x y = max-cong refl (λ i → dᵢ-sym (x i) (y i))
    
      d-cong : (∀ {i} → dᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
               d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
      d-cong dᵢ-cong m≈n p≈q = max-cong refl (λ i → dᵢ-cong (m≈n i) (p≈q i))

      d≡0⇒x≈y : (∀ {i} {xᵢ yᵢ : Sᵢ i} → dᵢ xᵢ yᵢ ≡ 0 → xᵢ ≈ᵢ yᵢ) → ∀ {x y} → d x y ≡ 0 → x ≈ y
      d≡0⇒x≈y dᵢ≡0⇒x≈y {x} {y} d≡0 i = dᵢ≡0⇒x≈y (≤-antisym (subst (dᵢ (x i) (y i) ≤_) d≡0 (dᵢ≤d x y i)) z≤n)

      x≈y⇒d≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → d x y ≡ 0
      x≈y⇒d≡0 x≈y⇒dᵢ≡0 x≈y = max-constant refl (λ i → x≈y⇒dᵢ≡0 (x≈y i))

      
      
      maxTriIneq : (∀ {i} → MaxTriangleIneq (𝕊ᵢ i) dᵢ) →
                   MaxTriangleIneq 𝕊 d
      maxTriIneq dᵢ-ineq x y z with max[t]∈t 0 λ i → dᵢ (x i) (z i)
      ... | inj₁ dxz≡0 = subst (_≤ d x y ⊔ d y z) (sym dxz≡0) z≤n
      ... | inj₂ (j , dxz≡dⱼxⱼzⱼ) = begin
        d x z                           ≡⟨ dxz≡dⱼxⱼzⱼ ⟩
        dᵢ (x j) (z j)                  ≤⟨ dᵢ-ineq _ _ _ ⟩
        dᵢ (x j) (y j) ⊔ dᵢ (y j) (z j) ≤⟨ ⊔-mono-≤ (dᵢ≤d x y j) (dᵢ≤d y z j) ⟩
        d x y ⊔ d y z                   ∎
        where open ≤-Reasoning

  bounded : {dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ} →
            (∀ {i} → Bounded (𝕊ᵢ i) dᵢ) → Bounded 𝕊 (d dᵢ)
  bounded dᵢ-bounded =
      (max 0 (λ i → proj₁ (dᵢ-bounded {i}))) ,
      (λ x y → max[s]≤max[t]₂ (≤-refl {0}) (λ i → proj₂ (dᵢ-bounded {i}) (x i) (y i)))
        
  isUltrametric : {dᵢ : ∀ {i} → Sᵢ i → Sᵢ i → ℕ} → (∀ {i} → IsUltrametric (𝕊ᵢ i) dᵢ) →
                  IsUltrametric 𝕊 (d dᵢ)
  isUltrametric {dᵢ} um = record
    { cong        = d-cong    dᵢ λ {i} → IsUltrametric.cong (um {i})
    ; eq⇒0        = x≈y⇒d≡0   dᵢ λ {i} → IsUltrametric.eq⇒0 (um {i})
    ; 0⇒eq        = d≡0⇒x≈y   dᵢ (λ {i} → IsUltrametric.0⇒eq (um {i}))
    ; sym         = d-sym      dᵢ λ {i} → IsUltrametric.sym (um {i})
    ; maxTriangle = maxTriIneq dᵢ λ {i} → IsUltrametric.maxTriangle (um {i})
    }

  ultrametric : (∀ i → Ultrametric (𝕊ᵢ i)) → Ultrametric 𝕊
  ultrametric um = record
    { d             = d (λ {i} → Ultrametric.d (um i))
    ; isUltrametric = isUltrametric (λ {i} → Ultrametric.isUltrametric (um i))
    }
