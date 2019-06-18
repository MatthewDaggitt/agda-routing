--------------------------------------------------------------------------------
-- Basic properties of an ACO
--------------------------------------------------------------------------------

open import Data.Fin.Subset using (Subset)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  {a ℓ n}
  (I∥ : AsyncIterable a ℓ n)
  {ℓ₁ ℓ₂ ℓ₃}
  {B₀ : IPred _ ℓ₁}
  {Q : Pred (Subset n) ℓ₂}
  (aco : PartialACO I∥ B₀ Q ℓ₃)
  where

open import Data.Fin using (Fin) renaming (_≟_ to _≟𝔽_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product as Prod using (∃; _,_; proj₂; proj₁)
open import Function using (_$_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import RoutingLib.Function
open import RoutingLib.Function.Reasoning
import RoutingLib.Relation.Nullary.Indexed.Replace as Replacement

open import RoutingLib.Iteration.Synchronous

open AsyncIterable I∥
open PartialACO aco

--------------------------------------------------------------------------------
-- Replacing one element of an indexed type with another

B-subst : ∀ {e f p q} → e ≡ f → p ≡ q → (p∈Q : p ∈ Q) (q∈Q : q ∈ Q) → B e p∈Q ≡ B f q∈Q
B-subst refl refl p∈Q q∈Q = refl

B₀ₑ-eqᵢ : ∀ {e p f q} (p∈Q : p ∈ Q) (q∈Q : q ∈ Q) → ∀ {i xᵢ} → xᵢ ∈ B e p∈Q 0 i → xᵢ ∈ B f q∈Q 0 i
B₀ₑ-eqᵢ {e} {p} {f} {q} p∈Q q∈Q {i} {xᵢ} xᵢ∈Bₑₚₖᵢ = begin⟨ xᵢ∈Bₑₚₖᵢ ⟩
  ∴ xᵢ ∈ B e p∈Q 0 i $⟨ proj₂ (B₀-eqᵢ p∈Q) ⟩
  ∴ xᵢ ∈ B₀ i        $⟨ proj₁ (B₀-eqᵢ q∈Q) ⟩
  ∴ xᵢ ∈ B f q∈Q 0 i ∎

B₀ₑ-eq : ∀ {e p f q} (p∈Q : p ∈ Q) (q∈Q : q ∈ Q) → ∀ {x} → x ∈ᵢ B e p∈Q 0 → x ∈ᵢ B f q∈Q 0
B₀ₑ-eq p∈Q q∈Q x∈Bₑₚ₀ i = B₀ₑ-eqᵢ p∈Q q∈Q (x∈Bₑₚ₀ i)

F-resp-B₀ₑ : ∀ {e p x} (p∈Q : p ∈ Q) → x ∈ᵢ B e p∈Q 0 → F e p x ∈ᵢ B e p∈Q 0
F-resp-B₀ₑ {e} {p} {x} p∈Q x∈Bₑₚ₀ = begin⟨ x∈Bₑₚ₀ ⟩
  ∴ x       ∈ᵢ B e p∈Q 0 $⟨ (λ prf i → proj₂ (B₀-eqᵢ p∈Q) (prf i)) ⟩
  ∴ x       ∈ᵢ B₀        $⟨ F-resp-B₀ p∈Q ⟩
  ∴ F e p x ∈ᵢ B₀        $⟨ (λ prf i → proj₁ (B₀-eqᵢ p∈Q) (prf i)) ⟩
  ∴ F e p x ∈ᵢ B e p∈Q 0 ∎

--------------------------------------------------------------------------------
-- Fixed points

module _ (e : Epoch) {p} (p∈Q : p ∈ Q) where

  x* : S
  x* = proj₁ (proj₂ (B-finish e p∈Q))

  k* : ℕ
  k* = proj₁ (B-finish e p∈Q)

  -- Properties

  B-cong : ∀ {k x y} → x ≈ y → x ∈ᵢ B e p∈Q k → y ∈ᵢ B e p∈Q k
  B-cong x≈y x∈Bₖ i = Bᵢ-cong p∈Q (x≈y i) (x∈Bₖ i)

  k*≤k⇒x*∈Bₖ : ∀ {k} → k* ≤ k → x* ∈ᵢ B e p∈Q k
  k*≤k⇒x*∈Bₖ k*≤k = proj₁ ((proj₂ (proj₂ (B-finish e p∈Q))) k*≤k)

  k*≤k∧x∈Bₖ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B e p∈Q k → x ≈ x*
  k*≤k∧x∈Bₖ⇒x≈x* k*≤k x∈Bₖ = proj₂ (proj₂ (proj₂ (B-finish e p∈Q)) k*≤k) x∈Bₖ

  open Replacement Sᵢ _≟𝔽_
  
  k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ : ∀ {k} → k* ≤ k → ∀ {i} {xᵢ : Sᵢ i} → xᵢ ∈ B e p∈Q k i → xᵢ ≈ᵢ x* i
  k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ {k} k*≤k {i} {xᵢ} xᵢ∈Bₖᵢ = begin⟨ k*≤k⇒x*∈Bₖ k*≤k ⟩
    ∴ x*             ∈ᵢ B e p∈Q k  $⟨ (λ p → ∈-replace (B e p∈Q k) p xᵢ∈Bₖᵢ) ⟩
    ∴ replace x* xᵢ   ∈ᵢ B e p∈Q k $⟨ k*≤k∧x∈Bₖ⇒x≈x* k*≤k ⟩
    ∴ replace x* xᵢ   ≈ x*         $⟨ _$ i ⟩
    ∴ replace x* xᵢ i ≈ᵢ x* i      $⟨ ≈ᵢ-trans (≈ᵢ-sym (≈ᵢ-reflexive (≡-replace x* xᵢ))) ⟩
    ∴ xᵢ              ≈ᵢ x* i      ∎

  x*∈Aₚ : x* ∈ Accordant p
  x*∈Aₚ i∉p = ≈ᵢ-sym (k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ ≤-refl (B-null p∈Q i∉p))

  x*-fixed : (F e p) x* ≈ x*
  x*-fixed = begin⟨ k*≤k⇒x*∈Bₖ ≤-refl ⟩
    ∴ x*         ∈ᵢ B e p∈Q k*       $⟨ F-mono-B p∈Q x*∈Aₚ ⟩
    ∴ F e p (x*) ∈ᵢ B e p∈Q (suc k*) $⟨ k*≤k∧x∈Bₖ⇒x≈x* (n≤1+n k*) ⟩
    ∴ F e p (x*) ≈ x*                ∎

  Fᵏx∈B₀ : ∀ k {x} → x ∈ᵢ B₀ → (F e p ^ k) x ∈ᵢ B₀
  Fᵏx∈B₀ zero    x∈B₀ = x∈B₀
  Fᵏx∈B₀ (suc k) x∈B₀ = F-resp-B₀ p∈Q (Fᵏx∈B₀ k x∈B₀)
