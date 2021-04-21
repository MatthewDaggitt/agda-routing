open import Data.Nat.Base as ℕ using (ℕ; s≤s; suc; _∸_)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Level using (Level; 0ℓ)
open import Data.Fin.Base
open import Data.Fin.Induction
open import Data.Fin.Properties
open import Induction.WellFounded
open import Relation.Binary
open import Function using (_on_; flip; _∘_)
open import Relation.Unary
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; trans; cong; sym; module ≡-Reasoning)

module RoutingLib.Data.Fin.Induction where

private
  variable
    ℓ : Level
    n : ℕ
    
_>_ : Rel (Fin n) 0ℓ
_>_ = ℕ._>_ on toℕ

>-wellFounded : WellFounded {A = Fin n} _>_
>-wellFounded {n} x = acc-map (ℕ.<-wellFounded (n ∸ toℕ x))
  where
  acc-map : ∀ {x : Fin n} → Acc ℕ._<_ (n ∸ toℕ x) → Acc _>_ x
  acc-map (acc rs) = acc (λ y y>x → acc-map (rs (n ∸ toℕ y) (ℕ.∸-monoʳ-< y>x (toℕ≤n y))))

<-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P zero → (∀ i → P (inject₁ i) → P (suc i)) →
                  ∀ i → P i
<-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁ i = ind (<-wellFounded i)
  where
  ind : ∀ {i} → Acc _<_ i → P i
  ind {zero}  _         = P₀
  ind {suc i} (acc rec) = Pᵢ⇒Pᵢ₊₁ i (ind (rec (inject₁ i) (s≤s (ℕ.≤-reflexive (toℕ-inject₁ i)))))

>-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P (fromℕ n) → (∀ i → P (suc i) → P (inject₁ i)) →
                  ∀ i → P i
>-weakInduction {n = n} P Pₙ Pᵢ₊₁⇒Pᵢ i = ind (>-wellFounded i)
  where
  ind : ∀ {i} → Acc _>_ i → P i
  ind {i} (acc rec) with n ℕ.≟ toℕ i 
  ... | yes n≡i = subst P (toℕ-injective (trans (toℕ-fromℕ n) n≡i)) Pₙ
  ... | no  n≢i = subst P
    (inject₁-lower₁ i n≢i)
    (Pᵢ₊₁⇒Pᵢ (lower₁ i n≢i) (ind (rec _ (s≤s (ℕ.≤-reflexive (sym (toℕ-lower₁ i n≢i)))))))
