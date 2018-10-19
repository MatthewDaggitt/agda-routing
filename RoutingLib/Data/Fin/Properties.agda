open import Algebra.FunctionProperties
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
open import Data.Product using (_,_)
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s; zero; suc) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans; subst₂; module ≡-Reasoning)
open import Relation.Binary.Consequences using (trans∧tri⟶resp≈)
open import Function using (_on_; _∘_; flip)
import Function.Bijection as Bijection

open import RoutingLib.Relation.Nullary using (Finite)

module RoutingLib.Data.Fin.Properties where

𝔽ₛ : ℕ → Setoid _ _
𝔽ₛ = setoid

-------------------------
-- Ordering properties --
-------------------------

-- stdlib
≤-respₗ-≡ : ∀ {n x} → ((_≤_ {n}) x) Respects _≡_
≤-respₗ-≡ refl x≤y = x≤y

-- stdlib
≤-respᵣ-≡ : ∀ {n x} → (flip (_≤_ {n}) x) Respects _≡_
≤-respᵣ-≡ refl x≤y = x≤y

-- stdlib
≤-resp₂-≡ : ∀ {n} → (_≤_ {n}) Respects₂ _≡_
≤-resp₂-≡ = ≤-respₗ-≡ , ≤-respᵣ-≡

------------------------------------------------------------------------
-- toℕ

toℕ-cancel-< : ∀ {n} {i j : Fin n} → toℕ i <ℕ toℕ j → i < j
toℕ-cancel-< i<j = i<j

toℕ-mono-< : ∀ {n} {i j : Fin n} → i < j → toℕ i <ℕ toℕ j
toℕ-mono-< i<j = i<j

------------------------------------------------------------------------
-- fromℕ

≤fromℕ : ∀ k → (i : Fin (suc k)) → i ≤ fromℕ k
≤fromℕ _       fzero    = z≤n
≤fromℕ zero    (fsuc ())
≤fromℕ (suc k) (fsuc i) = s≤s (≤fromℕ k i)

------------------------------------------------------------------------
-- fromℕ≤

fromℕ≤-cong : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
               i ≡ j → fromℕ≤ i<n ≡ fromℕ≤ j<n
fromℕ≤-cong i<n j<n refl = cong fromℕ≤ (ℕₚ.≤-irrelevance i<n j<n)

fromℕ≤-injective : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                    fromℕ≤ i<n ≡ fromℕ≤ j<n → i ≡ j
fromℕ≤-injective (s≤s z≤n)       (s≤s z≤n)       eq = refl
fromℕ≤-injective (s≤s z≤n)       (s≤s (s≤s j<n)) ()
fromℕ≤-injective (s≤s (s≤s i<n)) (s≤s z≤n)       ()
fromℕ≤-injective (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) eq =
  cong suc (fromℕ≤-injective (s≤s i<n) (s≤s j<n) (suc-injective eq))

fromℕ≤-mono-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                 i ≤ℕ j → fromℕ≤ i<n ≤ fromℕ≤ j<n
fromℕ≤-mono-≤ (s≤s z≤n)       (s≤s _)         z≤n       = z≤n
fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s z≤n)       ()
fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) (s≤s i≤j) =
  s≤s (fromℕ≤-mono-≤ (s≤s i<n) (s≤s j<n) i≤j)

fromℕ≤-cancel-< : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                  fromℕ≤ i<n < fromℕ≤ j<n → i <ℕ j
fromℕ≤-cancel-< i<n j<n i<j = subst₂ _<ℕ_ (toℕ-fromℕ≤ i<n) (toℕ-fromℕ≤ j<n) i<j

------------------------------------------------------------------------
-- fromℕ≤″

fromℕ≤″-cong : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
               i ≡ j → fromℕ≤″ i i<n ≡ fromℕ≤″ j j<n
fromℕ≤″-cong i<n j<n eq =
  subst₂ _≡_
    (fromℕ≤≡fromℕ≤″ (ℕₚ.≤″⇒≤ i<n) i<n)
    (fromℕ≤≡fromℕ≤″ (ℕₚ.≤″⇒≤ j<n) j<n)
    (fromℕ≤-cong _ _ eq)

fromℕ≤″-toℕ : ∀ {n} {i : Fin n} (toℕ<n : toℕ i ℕ.<″ n) →
                fromℕ≤″ (toℕ i) toℕ<n ≡ i
fromℕ≤″-toℕ {n} {i} toℕ<n = begin
  fromℕ≤″ (toℕ i) _ ≡⟨ sym (fromℕ≤≡fromℕ≤″ _ toℕ<n) ⟩
  fromℕ≤ _           ≡⟨ fromℕ≤-toℕ i (ℕₚ.≤″⇒≤ toℕ<n) ⟩
  i ∎
  where open ≡-Reasoning

fromℕ≤″-injective : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
                    fromℕ≤″ i i<n ≡ fromℕ≤″ j j<n → i ≡ j
fromℕ≤″-injective i<n j<n eq = fromℕ≤-injective _ _ (subst₂ _≡_
    (sym (fromℕ≤≡fromℕ≤″ (ℕₚ.≤″⇒≤ i<n) i<n))
    (sym (fromℕ≤≡fromℕ≤″ (ℕₚ.≤″⇒≤ j<n) j<n))
    eq)

-- stdlib
toℕ-fromℕ≤″ : ∀ {m n} (m<n : m ℕ.<″ n) → toℕ (fromℕ≤″ m m<n) ≡ m
toℕ-fromℕ≤″ {m} {n} m<n = begin
  toℕ (fromℕ≤″ m m<n)  ≡⟨ cong toℕ (sym (fromℕ≤≡fromℕ≤″ _ m<n)) ⟩
  toℕ (fromℕ≤ _)       ≡⟨ toℕ-fromℕ≤ (ℕₚ.≤″⇒≤ m<n) ⟩
  m ∎
  where open ≡-Reasoning


finite : ∀ n → Finite (Fin n)
finite n = n , Bijection.id



-----------
-- Other --
-----------

suc≢zero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
suc≢zero ()

≰⇒≢ : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → m ≢ n
≰⇒≢ m≰n refl = m≰n ≤-refl

