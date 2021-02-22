--------------------------------------------------------------------------------
-- Basic properties of an ACO
--------------------------------------------------------------------------------

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product as Prod using (∃; _×_; _,_; proj₂; proj₁)
open import Function using (_$_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Function.Reasoning
import RoutingLib.Relation.Nullary.Indexed.Replace as Replacement

open import RoutingLib.Iteration.Synchronous
open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  {a ℓ n}
  (I∥ : AsyncIterable a ℓ n) (open AsyncIterable I∥)
  {ℓ₁ ℓ₂ ℓ₃}
  {X₀ : IPred Sᵢ ℓ₁}
  {Q  : Pred (Epoch × Subset n) ℓ₂}
  (partialACO : PartialACO I∥ X₀ Q ℓ₃)
  where

open PartialACO partialACO

private
  variable
    e f : Epoch
    p q : Subset n

--------------------------------------------------------------------------------
-- Replacing one element of an indexed type with another

module _ {e p f q} (ep∈Q : (e , p) ∈ Q) (fq∈Q : (f , q) ∈ Q) where


  B₁ = LocalACO.B (localACO ep∈Q)
  B₂ = LocalACO.B (localACO fq∈Q)
  
  B-subst : e ≡ f → p ≡ q → B₁ ≡ B₂
  B-subst refl refl = refl
  
--------------------------------------------------------------------------------
-- Fixed points

module _ {e} {p} (ep∈Q : (e , p) ∈ Q) where

  open LocalACO (localACO ep∈Q)
  
  x* : S
  x* = proj₁ $ proj₂ B-finish

  k* : ℕ
  k* = proj₁ B-finish

  -- Properties

  x*∈X₀ : x* ∈ᵢ X₀
  x*∈X₀ = proj₁ $ proj₂ $ proj₂ B-finish
  
  k*≤k⇒x*∈Bₖ : ∀ {k} → k* ≤ k → x* ∈ᵢ B k
  k*≤k⇒x*∈Bₖ k*≤k = proj₁ $ (proj₂ $ proj₂ $ proj₂ B-finish) k*≤k

  k*≤k∧x∈Bₖ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  k*≤k∧x∈Bₖ⇒x≈x* k*≤k = proj₂ $ (proj₂ $ proj₂ $ proj₂ B-finish) k*≤k

  open Replacement Sᵢ _≟𝔽_
  
  k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ : ∀ {k} → k* ≤ k → ∀ {i} {xᵢ : Sᵢ i} → xᵢ ∈ B k i → xᵢ ≈ᵢ x* i
  k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ {k} k*≤k {i} {xᵢ} xᵢ∈Bₖᵢ = begin⟨ k*≤k⇒x*∈Bₖ k*≤k ⟩
    ∴ x*              ∈ᵢ B k       $⟨ (λ p → ∈-replace (B k) p xᵢ∈Bₖᵢ) ⟩
    ∴ replace x* xᵢ   ∈ᵢ B k       $⟨ k*≤k∧x∈Bₖ⇒x≈x* k*≤k ⟩
    ∴ replace x* xᵢ   ≈ x*         $⟨ _$ i ⟩
    ∴ replace x* xᵢ i ≈ᵢ x* i      $⟨ ≈ᵢ-trans (≈ᵢ-sym (≈ᵢ-reflexive (≡-replace x* xᵢ))) ⟩
    ∴ xᵢ              ≈ᵢ x* i      ∎

  x*∈Aₚ : x* ∈ Accordant p
  x*∈Aₚ i∉p = ≈ᵢ-sym (k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ ≤-refl (B-null i∉p))
  
  x*-fixed : (F e p) x* ≈ x*
  x*-fixed = begin⟨ k*≤k⇒x*∈Bₖ ≤-refl ⟩
    ∴ x*         ∈ᵢ B k*       $⟨ F-mono-B x*∈X₀ x*∈Aₚ ⟩
    ∴ F e p (x*) ∈ᵢ B (suc k*) $⟨ k*≤k∧x∈Bₖ⇒x≈x* (n≤1+n k*) ⟩
    ∴ F e p (x*) ≈ x*          ∎
  
  localFP : LocalFixedPoint I∥ e p
  localFP = record
    { x*       = x*
    ; k*       = k*
    ; x*-fixed = x*-fixed
    }

  B-cong : ∀ {k x y} → x ≈ y → x ∈ᵢ B k → y ∈ᵢ B k
  B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)
