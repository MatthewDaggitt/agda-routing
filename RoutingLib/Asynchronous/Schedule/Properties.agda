open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _∸_; _+_; z≤n; s≤s; _≟_; _≤?_)
open import Data.Nat.Properties using (∸-+-assoc; m≤m+n; ≰⇒>; n∸n≡0; +-∸-assoc; ≤-trans; ≤-refl; ≰⇒≥; +-∸-comm)
open import Data.Nat.Properties.Simple using (+-assoc; +-comm; +-right-identity)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Product using (∃; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; subst; cong; cong₂; _≢_; _≡_; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m+o≡n)

module RoutingLib.Asynchronous.Schedule.Properties where

  open Schedule
  open ≡-Reasoning
{-
  abstract

    --------------------------
    -- Activation functions --
    --------------------------

    ≈𝔸-refl : ∀ {n} (α : 𝔸 n) t → α ⟦ t ⟧≈𝔸⟦ t ⟧ α
    ≈𝔸-refl _ _ _ = refl

    ≈𝔸-sym  : ∀ {n} (α₁ α₂ : 𝔸 n) {t₁ t₂} → α₁ ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ α₂ → α₂ ⟦ t₂ ⟧≈𝔸⟦ t₁ ⟧ α₁
    ≈𝔸-sym _ _ α₁≈α₂ t = sym (α₁≈α₂ t)

    ≈𝔸-trans : ∀ {n} {α₁ α₂ α₃ : 𝔸 n} {t₁ t₂ t₃} → α₁ ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ α₂ → α₂ ⟦ t₂ ⟧≈𝔸⟦ t₃ ⟧ α₃ → α₁ ⟦ t₁ ⟧≈𝔸⟦ t₃ ⟧ α₃
    ≈𝔸-trans α₁≈α₂ α₂≈α₃ t = trans (α₁≈α₂ t) (α₂≈α₃ t)

    ≈𝔸-fastForward : ∀ {n} {α₁ α₂ : 𝔸 n} {t₁ t₂} → α₁ ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ α₂ → ∀ t → α₁ ⟦ t + t₁ ⟧≈𝔸⟦ t + t₂ ⟧ α₂
    ≈𝔸-fastForward {t₁ = t₁} {t₂} eq t t' rewrite sym (+-assoc t' t t₁) | sym (+-assoc t' t t₂) = eq (t' + t)

    ≈𝔸-starvationFree : ∀ {n} {α₁ α₂ : 𝔸 n} → StarvationFree α₁ → ∀ {t₁ t₂} → α₁ ⟦ t₁ ⟧≈𝔸⟦ t₂ ⟧ α₂ → StarvationFree α₂
    ≈𝔸-starvationFree {_} {α₁} {α₂} sf {t₁} {t₂} α-eq t i with sf (t + t₁) i
    ... | (t' , t+t₁<t' , i∈αₜ') with m≤n⇒m+o≡n t+t₁<t'
    ...   | (o , refl) = suc t + (o + t₂) , m≤m+n (suc t) (o + t₂) , subst (i ∈_) (
      (begin
        α₁ (suc t + t₁ + o)   ≡⟨ cong α₁ (+-assoc (suc t) t₁ o) ⟩
        α₁ (suc t + (t₁ + o)) ≡⟨ cong (λ v → α₁ (suc t + v)) (+-comm t₁ o) ⟩
        α₁ (suc t + (o + t₁)) ≡⟨ cong α₁ (sym (+-assoc (suc t) o t₁)) ⟩
        α₁ (suc t + o + t₁)   ≡⟨ α-eq (t + o) ⟩
        α₂ (suc t + o + t₂)   ≡⟨ cong α₂ (+-assoc (suc t) o t₂) ⟩
        α₂ (suc t + (o + t₂))
      ∎)) i∈αₜ'

    ≈𝔸-appTrans : ∀ {n} (f g : 𝔸 n → 𝔸 n) {t₁ t₂} → (∀ α → α ⟦ 0 ⟧≈𝔸⟦ t₁ ⟧ f α) → (∀ α → α ⟦ 0 ⟧≈𝔸⟦ t₂ ⟧ g α) → ∀ α → α ⟦ 0 ⟧≈𝔸⟦ t₁ + t₂ ⟧ f (g α)  
    ≈𝔸-appTrans f g {t₁} {t₂} α≈fα α≈gα α t =
      begin
        α (suc t + 0)               ≡⟨ α≈gα α t ⟩
        g α (suc t + t₂)            ≡⟨ cong (g α) (sym (+-right-identity _)) ⟩
        g α (suc t + t₂ + 0)        ≡⟨ α≈fα (g α) (t + t₂) ⟩
        f (g α) (suc t + t₂ + t₁)   ≡⟨ cong (f (g α)) (+-assoc (suc t) t₂ t₁) ⟩
        f (g α) (suc t + (t₂ + t₁)) ≡⟨ cong (λ v → f (g α) (suc t + v)) (+-comm t₂ t₁)  ⟩
        f (g α) (suc t + (t₁ + t₂))
      ∎


    -------------------------
    -- Data flow functions --
    -------------------------

    ≈𝔹-refl : ∀ {n} {β : 𝔹 n} {t} → β ⟦ t ⟧≈𝔹⟦ t ⟧ β
    ≈𝔹-refl _ _ _ = refl

    ≈𝔹-sym  : ∀ {n} (β₁ β₂ : 𝔹 n) {t₁ t₂} → β₁ ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ β₂ → β₂ ⟦ t₂ ⟧≈𝔹⟦ t₁ ⟧ β₁
    ≈𝔹-sym _ _ β₁≈β₂ t i j = sym (β₁≈β₂ t i j)

    ≈𝔹-trans : ∀ {n} {β₁ β₂ β₃ : 𝔹 n} {t₁ t₂ t₃} → β₁ ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ β₂ → β₂ ⟦ t₂ ⟧≈𝔹⟦ t₃ ⟧ β₃ → β₁ ⟦ t₁ ⟧≈𝔹⟦ t₃ ⟧ β₃
    ≈𝔹-trans β₁≈β₂ β₂≈β₃ t i j = trans (β₁≈β₂ t i j) (β₂≈β₃ t i j)

    ≈𝔹-fastForward : ∀ {n} {β₁ β₂ : 𝔹 n} {t₁ t₂} → β₁ ⟦ t₁ ⟧≈𝔹⟦ t₂ ⟧ β₂ → ∀ t → β₁ ⟦ t + t₁ ⟧≈𝔹⟦ t + t₂ ⟧ β₂
    ≈𝔹-fastForward {_} {β₁} {β₂} {t₁} {t₂} eq t t' i j =
      begin
        β₁ (suc t' + (t + t₁)) i j ∸ (t + t₁) ≡⟨ cong₂ _∸_ (cong (λ t → β₁ t i j) (sym (+-assoc (suc t') t t₁))) (+-comm t t₁) ⟩
        β₁ ((suc t' + t) + t₁) i j ∸ (t₁ + t) ≡⟨ sym (∸-+-assoc (β₁ (suc t' + t + t₁) i j) t₁ t) ⟩
        β₁ ((suc t' + t) + t₁) i j ∸ t₁ ∸ t   ≡⟨ cong (_∸ t) (eq (t' + t) i j) ⟩
        β₂ ((suc t' + t) + t₂) i j ∸ t₂ ∸ t   ≡⟨ ∸-+-assoc (β₂ (suc t' + t + t₂) i j) t₂ t ⟩
        β₂ ((suc t' + t) + t₂) i j ∸ (t₂ + t) ≡⟨ cong₂ _∸_ (cong (λ t → β₂ t i j) (+-assoc (suc t') t t₂)) (+-comm t₂ t) ⟩
        β₂ (suc t' + (t + t₂)) i j ∸ (t + t₂)
     ∎
    
    ≈𝔹-appTrans : ∀ {n} (f g : 𝔹 n → 𝔹 n) t₁ t₂ → (∀ β → β ⟦ 0 ⟧≈𝔹⟦ t₁ ⟧ f β) → (∀ β → β ⟦ 0 ⟧≈𝔹⟦ t₂ ⟧ g β) → ∀ β → β ⟦ 0 ⟧≈𝔹⟦ t₁ + t₂ ⟧ f (g β)  
    ≈𝔹-appTrans f g t₁ t₂ β≈fβ β≈gβ β t i j = sym (
      begin
        f (g β) (suc t + (t₁ + t₂)) i j ∸ (t₁ + t₂)   ≡⟨ sym (∸-+-assoc _ t₁ t₂) ⟩
        f (g β) (suc t + (t₁ + t₂)) i j ∸ t₁ ∸ t₂     ≡⟨ cong (λ v → f (g β) (suc t + v) i j ∸ t₁ ∸ t₂) (+-comm t₁ t₂) ⟩
        f (g β) (suc t + (t₂ + t₁)) i j ∸ t₁ ∸ t₂     ≡⟨ sym (cong (λ t → f (g β) t i j ∸ t₁ ∸ t₂) (+-assoc (suc t) t₂ t₁)) ⟩
        f (g β) (suc t + t₂ + t₁) i j ∸ t₁ ∸ t₂       ≡⟨ sym (cong (_∸ t₂) (β≈fβ (g β) (t + t₂) i j)) ⟩
        g β (suc t + t₂ + 0) i j ∸ t₂                 ≡⟨ cong (λ t → g β t i j ∸ t₂) (+-right-identity (suc t + t₂)) ⟩
        g β (suc t + t₂) i j ∸ t₂                     ≡⟨ sym (β≈gβ β t i j) ⟩
        β (suc t + 0) i j   
      ∎)

    ---------------
    -- Schedules --
    ---------------

    ⟦⟧≈⟦⟧-fastForward : ∀ {n} {𝕤₁ 𝕤₂ : Schedule n} {t₁ t₂} → 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ → ∀ t → 𝕤₁ ⟦ t + t₁ ⟧≈⟦ t + t₂ ⟧ 𝕤₂
    ⟦⟧≈⟦⟧-fastForward {_} {𝕤₁} {𝕤₂} (α-eq , β-eq) t = ≈𝔸-fastForward {_} {α 𝕤₁} {α 𝕤₂} α-eq t , ≈𝔹-fastForward {_} {β 𝕤₁} {β 𝕤₂} β-eq t
-}
