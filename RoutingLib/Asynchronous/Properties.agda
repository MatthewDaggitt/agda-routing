open import Data.Nat using (ℕ; _≤_; _<_; _≤′_; zero; suc; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Dec using (_∈?_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; _≗_; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule using (Schedule; previousActivation)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Data.Nat.Properties using (≤-refl; ≤-antisym; ≤-stepdown; ≤+≢⇒<; ≤-trans)

module RoutingLib.Asynchronous.Properties {a ℓ n} (f : Parallelisation a ℓ n) (sch : Schedule n) where
  
  open Parallelisation f
  open Schedule sch

  abstract
    t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ : ∀ X {s t} → s ≡ t → (tAcc : Acc _<_ t) → (sAcc : Acc _<_ s) → δ^' f sch tAcc X ≈ₘ δ^' f sch sAcc X
    t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ X {zero}  refl (acc tAcc) (acc sAcc) = ≈ₘ-refl
    t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ X {suc t} refl (acc tAcc) (acc sAcc) i with i ∈? α (suc t)
    ... | yes _ = σᵢ-cong (λ k → t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ X refl (tAcc (β (suc t) i k) (causality t i k)) (sAcc (β (suc t) i k) (causality t i k)) k)
    ... | no  _ = t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ X refl (tAcc t ≤-refl) (sAcc t ≤-refl) i

    δᵢ'-constantSinceActivation : ∀ X {t} (tAcc : Acc _<_ t) i {p} (pAcc : Acc _<_ p) → p ≤ t → (∀ {t'} → t' ≤ t → i ∈ α t' → t' ≤ p) → δ^' f sch tAcc X i ≈ᵢ δ^' f sch pAcc X i
    δᵢ'-constantSinceActivation X {zero}  _          i {_} pAcc z≤n p-latest = ≈ᵢ-refl
    δᵢ'-constantSinceActivation X {suc t} (acc tAcc) i {p} pAcc p≤t+1 p-latest with p ≟ suc t 
    ... | yes p≡t+1 = t≡s⇒δ'ᵗᵢ≈δ'ˢᵢ X p≡t+1 (acc tAcc) pAcc i
    ... | no  p≢t+1 with i ∈? α (suc t) 
    ... | no  _     = δᵢ'-constantSinceActivation X (tAcc t ≤-refl) i pAcc (≤-stepdown (≤+≢⇒< p≤t+1 p≢t+1)) (λ t'≤t → p-latest (≤-trans t'≤t (n≤1+n _)))
    ... | yes i∈αₜ₊₁ = contradiction (p-latest ≤-refl i∈αₜ₊₁) (λ t+1≤p → p≢t+1 (≤-antisym p≤t+1 t+1≤p))

    δᵢ-constantSinceActivation : ∀ {t p} X i → p ≤ t → (∀ {t'} → t' ≤ t → i ∈ α t' → t' ≤ p) → δ^ f sch t X i ≈ᵢ δ^ f sch p X i
    δᵢ-constantSinceActivation {t} {p} X i p≤t p-latest = δᵢ'-constantSinceActivation X (<-wf t) i (<-wf p) p≤t p-latest
