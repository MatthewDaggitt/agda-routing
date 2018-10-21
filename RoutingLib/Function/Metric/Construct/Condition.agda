open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (if_then_else_)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

module RoutingLib.Function.Metric.Construct.Condition
  {a} {A : Set a} (d : A → A → ℕ)
  {b p} {B : Set b} {P : Pred B p} (P? : Decidable P) where

dᶜ : B → A → A → ℕ
dᶜ c x y = if ⌊ P? c ⌋ then d x y else 0

cong : ∀ {ℓ} {_≈_ : Rel A ℓ} → d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_ →
       ∀ c {w x y z : A} → (P c → w ≈ x) → (P c → y ≈ z) → dᶜ c w y ≡ dᶜ c x z
cong pres c w≈x y≈z with P? c
... | yes P = pres (w≈x P) (y≈z P)
... | no  _ = refl

cong′ : ∀ {ℓ} {_≈_ : Rel A ℓ} → (d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_) →
        ∀ c → (dᶜ c Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_)
cong′ pres c w≈x y≈z = cong pres c (λ _ → w≈x) (λ _ → y≈z)

x≈y⇒≡0 : ∀ {ℓ} {_≈_ : Rel A ℓ} →
         (∀ {x y} → x ≈ y → d x y ≡ 0) →
         ∀ {c x y} → x ≈ y → dᶜ c x y ≡ 0
x≈y⇒≡0 eq {c} x≈y with P? c
... | yes _ = eq x≈y
... | no  _ = refl

sym : (∀ x y → d x y ≡ d y x) → ∀ c x y → dᶜ c x y ≡ dᶜ c y x
sym sym c x y with P? c
... | yes _ = sym x y
... | no  _ = refl

P⇒dᶜ≡d : ∀ {c} → P c → ∀ x y → dᶜ c x y ≡ d x y
P⇒dᶜ≡d {c} P x y with P? c
... | yes _ = refl
... | no ¬P = contradiction P ¬P

cond-eq' : ∀ c {x y : A} → (¬ P c → d x y ≡ 0) → dᶜ c x y ≡ d x y
cond-eq' c eq with P? c
... | yes _ = refl
... | no ¬P = P.sym (eq ¬P)

dᶜ≤d : ∀ {c} (x y : A) → dᶜ c x y ≤ d x y
dᶜ≤d {c} x y with P? c
... | yes _ = ≤-refl
... | no  _ = z≤n

