open import Data.Fin using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product as Prod using (∃; _,_; proj₂; proj₁)
open import Function using (_$_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Function
open import RoutingLib.Function.Reasoning
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Synchronous
open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO
  {a ℓ n p}
  (𝓘 : AsyncIterable a ℓ n)
  (aco : ACO 𝓘 p)
  (e : Epoch)
  (p : Subset n)
  where

open AsyncIterable 𝓘
open ACO aco

replace : S → ∀ {i} (xᵢ : Sᵢ i) → S
replace x {i} xᵢ j with i ≟𝔽 j
... | yes refl = xᵢ
... | no  _    = x j

∈-replace : ∀ {p} (P : IPred Sᵢ p) {x i} {xᵢ : Sᵢ i} → x ∈ P → xᵢ ∈ᵢ P → replace x xᵢ ∈ P
∈-replace P {i = i} x∈P xᵢ∈P j with i ≟𝔽 j
... | yes refl = xᵢ∈P
... | no  _    = x∈P j

≈ᵢ-replace : ∀ x {i} (xᵢ : Sᵢ i) → replace x xᵢ i ≈ᵢ xᵢ
≈ᵢ-replace x {i} xᵢ with i ≟𝔽 i
... | yes refl = ≈ᵢ-refl
... | no  i≢i  = contradiction refl i≢i

------------------------------------------------------------------------
-- Fixed points

x* : S
x* = proj₁ (proj₂ (B-finish e p))

k* : ℕ
k* = proj₁ (B-finish e p)

-- Properties

B-cong : ∀ {k x y} → x ≈ y → x ∈ B e p k → y ∈ B e p k
B-cong x≈y x∈Bₖ i = Bᵢ-cong (x≈y i) (x∈Bₖ i)

k*≤k⇒x*∈Bₖ : ∀ {k} → k* ≤ k → x* ∈ B e p k
k*≤k⇒x*∈Bₖ k*≤k = proj₁ ((proj₂ (proj₂ (B-finish e p))) k*≤k)

k*≤k∧x∈Bₖ⇒x≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ B e p k → x ≈ x*
k*≤k∧x∈Bₖ⇒x≈x* k*≤k x∈Bₖ = proj₂ (proj₂ (proj₂ (B-finish e p)) k*≤k) x∈Bₖ

k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ : ∀ {k} → k* ≤ k → ∀ {i} {xᵢ : Sᵢ i} → xᵢ ∈ᵢ B e p k → xᵢ ≈ᵢ x* i
k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ {k} k*≤k {i} {xᵢ} xᵢ∈Bₖᵢ = begin⟨ k*≤k⇒x*∈Bₖ k*≤k ⟩
  ⇒ x*             ∈ B e p k ∴⟨ ∈-replace (B e p k) ◌ xᵢ∈Bₖᵢ ⟩
  ⇒ replace x* xᵢ   ∈ B e p k ∴⟨ k*≤k∧x∈Bₖ⇒x≈x* k*≤k ⟩
  ⇒ replace x* xᵢ   ≈ x*      ∴⟨ _$ i ⟩
  ⇒ replace x* xᵢ i ≈ᵢ x* i    ∴⟨ ≈ᵢ-trans (≈ᵢ-sym (≈ᵢ-replace x* xᵢ)) ⟩ 
  ⇒ xᵢ              ≈ᵢ x* i    ∎

x*-wf : WellFormed p x*
x*-wf i∉p = ≈ᵢ-sym (k*≤k∧x∈Bₖᵢ⇒x≈x*ᵢ ≤-refl (B-null i∉p))

x*-fixed : (F e p) x* ≈ x*
x*-fixed = begin⟨ k*≤k⇒x*∈Bₖ ≤-refl ⟩
  ⇒ x*         ∈ B e p k*       ∴⟨ F-mono-B x*-wf ⟩
  ⇒ F e p (x*) ∈ B e p (suc k*) ∴⟨ k*≤k∧x∈Bₖ⇒x≈x* (n≤1+n k*) ⟩
  ⇒ F e p (x*) ≈ x*             ∎ 

Fᵏx∈B₀ : ∀ k {x} → x ∈ B e p 0 → (F e p ^ k) x ∈ B e p 0
Fᵏx∈B₀ zero    x∈B₀ = x∈B₀
Fᵏx∈B₀ (suc k) x∈B₀ = F-resp-B₀ (Fᵏx∈B₀ k x∈B₀)

postulate Fᵏx∈Bₖ : ∀ k {x} → WellFormed p x → x ∈ B e p 0 → (F e p ^ k) x ∈ B e p k
{-
Fᵏx∈Bₖ zero    x-wf x∈B₀ = x∈B₀
Fᵏx∈Bₖ (suc k) x-wf x∈B₀ = F-mono-B {!!} (Fᵏx∈Bₖ k x-wf x∈B₀)
-}

postulate k*≤k⇒Fᵏx≈x* : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ B e p 0 → (F e p ^ k) x ≈ x*
-- k*≤k⇒Fᵏx≈x* {k} k*≤k x∈B₀ = k*≤k∧x∈Bₖ⇒x≈x* k*≤k (Fᵏx∈Bₖ k {!!} x∈B₀)

x*∈B₀ : (∃ λ x → x ∈ B e p 0) → x* ∈ B e p 0
x*∈B₀ (x , x∈B₀) = begin⟨ x∈B₀ ⟩
  ⇒ x              ∈ B e p 0 ∴⟨ Fᵏx∈B₀ k* ⟩
  ⇒ (F e p ^ k*) x ∈ B e p 0 ∴⟨ B-cong (k*≤k⇒Fᵏx≈x* ≤-refl x∈B₀) ⟩
  ⇒ x*             ∈ B e p 0 ∎

x*∈Bₖ : (∃ λ x → x ∈ B e p 0) → ∀ k → x* ∈ B e p k
x*∈Bₖ ∃x∈B₀ zero    = x*∈B₀ ∃x∈B₀
x*∈Bₖ ∃x∈B₀ (suc k) = begin⟨ x*∈Bₖ ∃x∈B₀ k ⟩
  ⇒ x* ∈ B e p k             ∴⟨ F-mono-B x*-wf ⟩
  ⇒ F e p x* ∈ B e p (suc k) ∴⟨ B-cong x*-fixed ⟩
  ⇒ x* ∈ B e p (suc k)       ∎
