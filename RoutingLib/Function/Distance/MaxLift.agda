open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; z≤n; suc; _⊔_)
open import Data.Nat.Properties using (≤-antisym; ⊔-mono-≤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_)
open import Relation.Binary using (Setoid; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Table using (Table; max; zipWith)
open import RoutingLib.Data.Table.Properties using (max-cong; t≤max[t]; max-constant)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
import RoutingLib.Data.Table.IndexedTypes as IndexedType
open import RoutingLib.Function.Distance

module RoutingLib.Function.Distance.MaxLift {a ℓ n} (S : Fin n → Setoid a ℓ) where

  open IndexedType S using (M; M-setoid; _≈_)

  module _ (i : Fin n) where

    open Setoid (S i) using () renaming (Carrier to Mᵢ) public

  module _ {i : Fin n} where
    open Setoid (S i) using () renaming (_≈_ to _≈ᵢ_) public

  module _ (dᵢ : ∀ {i} → Mᵢ i → Mᵢ i → ℕ) where
  
    d : M → M → ℕ
    d x y = max 0 (λ i → dᵢ (x i) (y i))

    abstract
  
      dᵢ≤d : ∀ x y i → dᵢ (x i) (y i) ≤ d x y
      dᵢ≤d x y = t≤max[t] 0 (λ i → dᵢ (x i) (y i))
    
      d-sym : (∀ {i} → Symmetric (S i) (dᵢ {i})) → Symmetric M-setoid d
      d-sym dᵢ-sym x y = max-cong refl (λ i → dᵢ-sym (x i) (y i))
    
      d-cong : (∀ {i} → dᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
               d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
      d-cong dᵢ-cong m≈n p≈q = max-cong refl (λ i → dᵢ-cong (m≈n i) (p≈q i))

      d≡0⇒x≈y : (∀ {i} {xᵢ yᵢ : Mᵢ i} → dᵢ xᵢ yᵢ ≡ 0 → xᵢ ≈ᵢ yᵢ) → ∀ {x y} → d x y ≡ 0 → x ≈ y
      d≡0⇒x≈y dᵢ≡0⇒x≈y {x} {y} d≡0 i = dᵢ≡0⇒x≈y (≤-antisym (subst (dᵢ (x i) (y i) ≤_) d≡0 (dᵢ≤d x y i)) z≤n)

      x≈y⇒d≡0 : (∀ {i} {xᵢ yᵢ : Mᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ xᵢ yᵢ ≡ 0) → ∀ {x y} → x ≈ y → d x y ≡ 0
      x≈y⇒d≡0 x≈y⇒dᵢ≡0 x≈y = max-constant refl (λ i → x≈y⇒dᵢ≡0 (x≈y i))
  
      postulate bounded : (∀ {i} → Bounded (S i) dᵢ) → Bounded M-setoid d
    
      maxTriIneq : (∀ {i} → MaxTriangleIneq (S i) dᵢ) →
                   MaxTriangleIneq M-setoid d
      maxTriIneq dᵢ-ineq x y z with max[t]∈t 0 λ i → dᵢ (x i) (z i)
      ... | inj₁ dxz≡0 = subst (_≤ d x y ⊔ d y z) (sym dxz≡0) z≤n
      ... | inj₂ (j , dxz≡dⱼxⱼzⱼ) = begin
        d x z                           ≡⟨ dxz≡dⱼxⱼzⱼ ⟩
        dᵢ (x j) (z j)                  ≤⟨ dᵢ-ineq _ _ _ ⟩
        dᵢ (x j) (y j) ⊔ dᵢ (y j) (z j) ≤⟨ ⊔-mono-≤ (dᵢ≤d x y j) (dᵢ≤d y z j) ⟩
        d x y ⊔ d y z                   ∎
        where open ≤-Reasoning

      isUltrametric : (∀ i → IsUltrametric (S i) dᵢ) → IsUltrametric M-setoid d
      isUltrametric um = record
        { cong        = d-cong λ {i} → IsUltrametric.cong (um i)
        ; eq⇒0        = x≈y⇒d≡0 λ {i} → IsUltrametric.eq⇒0 (um i)
        ; 0⇒eq        = d≡0⇒x≈y (λ {i} → IsUltrametric.0⇒eq (um i))
        ; sym         = d-sym λ {i} → IsUltrametric.sym (um i)
        ; maxTriangle = maxTriIneq λ {i} → IsUltrametric.maxTriangle (um i)
        }

  ultrametric : (∀ i → Ultrametric (S i)) → Ultrametric M-setoid
  ultrametric um = record
    { d             = d (λ {i} → Ultrametric.d (um i))
    ; isUltrametric = isUltrametric (λ {i} → Ultrametric.d (um i)) (λ i → Ultrametric.isUltrametric (um i))
    }
