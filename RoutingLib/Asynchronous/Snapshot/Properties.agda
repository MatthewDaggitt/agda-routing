open import Data.Nat using (ℕ; _≤_; _≤?_; _<_; _+_; _∸_; zero; suc; z≤n; s≤s; _≟_; ≤-pred)
open import Data.Nat.Properties using (n≤1+n; ≰⇒>; +-∸-assoc; n∸n≡0)
open import Data.Nat.Properties.Simple using (+-right-identity; +-assoc)
open import Data.Fin.Subset using (_∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Product using (∃; _,_; _×_)
open import Relation.Binary using (_Preserves_⟶_; _⇒_; Reflexive; Symmetric; Transitive; Decidable; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans; _≗_; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule using (Schedule)
open import RoutingLib.Data.Table using (Table)


module RoutingLib.Asynchronous.Snapshot.Properties {a ℓ n} {S : Table (Setoid a ℓ) n}(p : Parallelisation S) where
{-
  open Parallelisation p
  open Schedule
  open import RoutingLib.Asynchronous.Properties p using (≈ₘ-trans; δ'-timeCong)


  abstract
    
    open import RoutingLib.Asynchronous.Snapshot p

    ≈ₛ⇒≈ₘ : σ Preserves _≈ₘ_ ⟶ _≈ₘ_ → ∀ {𝕤₁ 𝕤₂ t₁ t₂} X₁ X₂ → 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ → snapshot 𝕤₁ t₁ X₁ ≈ₛ snapshot 𝕤₂ t₂ X₂ → 
              δ 𝕤₁ t₁ X₁ ≈ₘ δ 𝕤₂ t₂ X₂ → ∀ t (t+t₁Acc : Acc _<_ (t + t₁)) (t+t₂Acc : Acc _<_ (t + t₂)) → δ' 𝕤₁ t+t₁Acc X₁ ≈ₘ δ' 𝕤₂ t+t₂Acc X₂
    ≈ₛ⇒≈ₘ σ-cong {𝕤₁} {𝕤₂} {t₁} {t₂} X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ zero   t₁Acc t₂Acc = ≈ₘ-trans (≈ₘ-trans (δ'-timeCong σ-cong 𝕤₁ X₁ refl t₁Acc (<-wf t₁)) δᵗ¹X₁≈δᵗ²X₂) (δ'-timeCong σ-cong 𝕤₂ X₂ refl (<-wf t₂) t₂Acc)
    ≈ₛ⇒≈ₘ σ-cong {𝕤₁} {𝕤₂} {t₁} {t₂} X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ (suc t) (acc t+t₁Acc) (acc t+t₂Acc) i with i ∈? α 𝕤₁ (suc (t + t₁)) | i ∈? α 𝕤₂ (suc (t + t₂))
    ... | no  _   | no _    = ≈ₛ⇒≈ₘ σ-cong X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ t (t+t₁Acc (t + t₁) ≤-refl) (t+t₂Acc (t + t₂) ≤-refl) i
    ... | yes i∈α | no  i∉α = contradiction (subst (i ∈_) (     α-eq (suc t))  i∈α) i∉α
    ... | no  i∉α | yes i∈α = contradiction (subst (i ∈_) (sym (α-eq (suc t))) i∈α) i∉α
    ... | yes _   | yes _   = σ-cong result i
      where
      result : ∀ k → δ' 𝕤₁ (t+t₁Acc (β 𝕤₁ (suc t + t₁) i k) _) X₁ k ≈ᵢ δ' 𝕤₂ (t+t₂Acc (β 𝕤₂ (suc t + t₂) i k) _) X₂ k
      result k with t₁ <? β 𝕤₁ (suc (t + t₁)) i k | t₂ <? β 𝕤₂ (suc (t + t₂)) i k
      ... | no  t₁≮β | no  t₂≮β = ≈ᵢ-trans (≈ᵢ-trans (δ'-timeCong σ-cong 𝕤₁ X₁ {β 𝕤₁ (suc t + t₁) i k} refl _ _ k) (snapshot-eq (suc t) i k (≮⇒≥ t₁≮β) (≮⇒≥ t₂≮β))) (δ'-timeCong σ-cong 𝕤₂ X₂ {β 𝕤₂ (suc t + t₂) i k} refl _ _ k)
      ... | no  t₁≮β | yes t₂<β = contradiction (trans (sym (β-eq t i k)) (m≤n⇒m∸n≡0 (≮⇒≥ t₁≮β))) (m>n⇒m∸n≢0 t₂<β)
      ... | yes t₁<β | no  t₂≮β = contradiction (trans      (β-eq t i k)  (m≤n⇒m∸n≡0 (≮⇒≥ t₂≮β))) (m>n⇒m∸n≢0 t₁<β)
      ... | yes t₁<β | yes t₂<β with w∸x≡y∸z⇒v+x≡w∧v+y≡z (β-eq t i k) (<⇒≤ t₁<β) (<⇒≤ t₂<β)
      ... | (o , o+t₁≡β , o+t₂≡β) = ≈ᵢ-trans (≈ᵢ-trans (δ'-timeCong σ-cong 𝕤₁ X₁ o+t₁≡β _ _ k) (≈ₛ⇒≈ₘ σ-cong X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ o (t+t₁Acc (o + t₁) (s≤s (≤-trans (≤-reflexive o+t₁≡β) (≤-pred (causality 𝕤₁ (t + t₁) i k))))) (<-wf (o + t₂)) k)) (δ'-timeCong σ-cong 𝕤₂ X₂ (sym o+t₂≡β) _ _ k)



-}
