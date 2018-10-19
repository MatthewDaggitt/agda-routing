open import Data.Nat using (ℕ)
open import Data.Bool using (if_then_else_)
open import Relation.Binary hiding (Decidable)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable using (⌊_⌋)

module RoutingLib.Function.Metric.Construct.Condition
  {a ℓ} {A : Set a} (_~_ : Rel A ℓ) (d : A → A → ℕ)
  {b p} {B : Set b} {P : Pred B p} (P? : Decidable P) where

dᶜ : B → A → A → ℕ
dᶜ c x y = if ⌊ P? c ⌋ then d x y else 0

cond-eq : ∀ {i} (x y : A) → i ∈ p → cond x y ≡ dᵢ x y
cond-eq {i} x y i∈p with i ∈? p
... | yes _  = refl
... | no i∉p = contradiction i∈p i∉p

cond-eq' : ∀ i {x y : Sᵢ i} → (i ∉ p → dᵢ x y ≡ 0) → cond x y ≡ dᵢ x y
cond-eq' i eq with i ∈? p
... | yes _   = refl
... | no  i∉p = sym (eq i∉p)

cond-leq : ∀ {i} (x y : Sᵢ i) → cond x y ≤ dᵢ x y
cond-leq {i} x y with i ∈? p
... | yes _ = ≤-refl
... | no  _ = z≤n

cond-sym : (∀ {i} → Symmetric (Setoid 𝕊 at i) (dᵢ {i})) → ∀ {i} (x y : Sᵢ i) → cond x y ≡ cond y x
cond-sym sym {i} x y with i ∈? p
... | yes _ = sym x y
... | no  _ = refl

cond-cong : (∀ {i} → dᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_) →
            ∀ i {w x y z : Sᵢ i} → (i ∈ p → w ≈ᵢ x) → (i ∈ p → y ≈ᵢ z) → cond w y ≡ cond x z
cond-cong pres i w≈x y≈z with i ∈? p
... | yes i∈p = pres (w≈x i∈p) (y≈z i∈p)
... | no  _   = refl

x≈y⇒cond≡0 : (∀ {i} {xᵢ yᵢ : Sᵢ i} → xᵢ ≈ᵢ yᵢ → dᵢ xᵢ yᵢ ≡ 0) →
             ∀ {i} {x y : Sᵢ i} → x ≈ᵢ y → cond x y ≡ 0
x≈y⇒cond≡0 eq {i} x≈y with i ∈? p
... | yes _ = eq x≈y
... | no  _ = refl
