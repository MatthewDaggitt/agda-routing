open import Algebra.FunctionProperties
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; z≤n; s≤s; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans; subst₂)
open import Relation.Binary.Consequences using (trans∧tri⟶resp≈)
open import Function using (_on_; _∘_; flip)

open import RoutingLib.Data.Fin

module RoutingLib.Data.Fin.Properties where

  𝔽ₛ : ℕ → Setoid _ _
  𝔽ₛ = setoid
  
  -- stdlib
  inject₁-injective : ∀ {n} {i j : Fin n} → inject₁ i ≡ inject₁ j → i ≡ j
  inject₁-injective {i = fzero}  {fzero}  i≡j = refl
  inject₁-injective {i = fzero}  {fsuc j} ()
  inject₁-injective {i = fsuc i} {fzero}  ()
  inject₁-injective {i = fsuc i} {fsuc j} i≡j = cong fsuc (inject₁-injective (suc-injective i≡j))


  -------------------------
  -- Ordering properties --
  -------------------------
  
  -- stdlib
  <⇒≤pred : ∀ {n} {i j : Fin n} → j < i → j ≤ pred i
  <⇒≤pred {_} {fzero} {_} ()
  <⇒≤pred {_} {fsuc i} {fzero} j<i = z≤n
  <⇒≤pred {_} {fsuc i} {fsuc j} (s≤s j<i) = subst (_ ≤ℕ_) (sym (inject₁-lemma i)) j<i

  -- stdlib
  ≤-respₗ-≡ : ∀ {n x} → ((_≤_ {n}) x) Respects _≡_
  ≤-respₗ-≡ refl x≤y = x≤y

  -- stdlib
  ≤-respᵣ-≡ : ∀ {n x} → (flip (_≤_ {n}) x) Respects _≡_
  ≤-respᵣ-≡ refl x≤y = x≤y

  -- stdlib
  ≤-resp₂-≡ : ∀ {n} → (_≤_ {n}) Respects₂ _≡_
  ≤-resp₂-≡ = ≤-respₗ-≡ , ≤-respᵣ-≡
  
  -- stdlib
  ≤+≢⇒< : ∀ {n} {i j : Fin n} → i ≤ j → i ≢ j → i < j
  ≤+≢⇒< {i = fzero}  {fzero}  _         0≢0     = contradiction refl 0≢0
  ≤+≢⇒< {i = fzero}  {fsuc j} _         _       = s≤s z≤n
  ≤+≢⇒< {i = fsuc i} {fzero}  ()
  ≤+≢⇒< {i = fsuc i} {fsuc j} (s≤s i≤j) 1+i≢1+j = s≤s (≤+≢⇒< i≤j (1+i≢1+j ∘ (cong fsuc)))

  toℕ-cancel-< : ∀ {n} {i j : Fin n} → toℕ i <ℕ toℕ j → i < j
  toℕ-cancel-< i<j = i<j
  
  toℕ-mono-< : ∀ {n} {i j : Fin n} → i < j → toℕ i <ℕ toℕ j
  toℕ-mono-< i<j = i<j


  -----------
  -- Other --
  -----------

  suc≢zero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
  suc≢zero ()

  <⇨≢ : ∀ {n₁} {m n : Fin n₁} → m < n → m ≢ n
  <⇨≢ m<n m≡n = (ℕₚ.<⇒≢ m<n) (cong toℕ m≡n)

  m≰n⇨m≢n : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → m ≢ n
  m≰n⇨m≢n m≰n refl = m≰n ℕₚ.≤-refl
  
  ≤fromℕ : ∀ k → (i : Fin (suc k)) → i ≤ fromℕ k
  ≤fromℕ _       fzero    = z≤n
  ≤fromℕ zero    (fsuc ())
  ≤fromℕ (suc k) (fsuc i) = s≤s (≤fromℕ k i)

  fromℕ≤-cong : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                 i ≡ j → fromℕ≤ i<n ≡ fromℕ≤ j<n
  fromℕ≤-cong i<n j<n refl = cong fromℕ≤ (ℕₚ.≤-irrelevance i<n j<n)

  fromℕ≤-mono-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                   i ≤ℕ j → fromℕ≤ i<n ≤ fromℕ≤ j<n
  fromℕ≤-mono-≤ (s≤s z≤n)       (s≤s _)         z≤n       = z≤n
  fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s z≤n)       ()
  fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) (s≤s i≤j) =
    s≤s (fromℕ≤-mono-≤ (s≤s i<n) (s≤s j<n) i≤j)

  fromℕ≤-mono⁻¹-< : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                    fromℕ≤ i<n < fromℕ≤ j<n → i <ℕ j 
  fromℕ≤-mono⁻¹-< i<n j<n i<j = subst₂ _<ℕ_ (toℕ-fromℕ≤ i<n) (toℕ-fromℕ≤ j<n) i<j
