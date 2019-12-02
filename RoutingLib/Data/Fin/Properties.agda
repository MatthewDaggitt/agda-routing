open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
open import Data.Product using (_,_)
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s; zero; suc) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans; subst₂; module ≡-Reasoning)
import Function.Bijection as Bijection

module RoutingLib.Data.Fin.Properties where

𝔽ₛ : ℕ → Setoid _ _
𝔽ₛ = ≡-setoid

------------------------------------------------------------------------
-- fromℕ

≤fromℕ : ∀ k → (i : Fin (suc k)) → i ≤ fromℕ k
≤fromℕ _       fzero    = z≤n
≤fromℕ (suc k) (fsuc i) = s≤s (≤fromℕ k i)

------------------------------------------------------------------------
-- fromℕ<

fromℕ<-cong : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
               i ≡ j → fromℕ< i<n ≡ fromℕ< j<n
fromℕ<-cong i<n j<n refl = cong fromℕ< (ℕₚ.≤-irrelevant i<n j<n)

fromℕ<-injective : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                    fromℕ< i<n ≡ fromℕ< j<n → i ≡ j
fromℕ<-injective (s≤s z≤n)       (s≤s z≤n)       eq = refl
fromℕ<-injective (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) eq =
  cong suc (fromℕ<-injective (s≤s i<n) (s≤s j<n) (suc-injective eq))

fromℕ<-mono-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                 i ≤ℕ j → fromℕ< i<n ≤ fromℕ< j<n
fromℕ<-mono-≤ (s≤s z≤n)       (s≤s _)         z≤n       = z≤n
fromℕ<-mono-≤ (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) (s≤s i≤j) =
  s≤s (fromℕ<-mono-≤ (s≤s i<n) (s≤s j<n) i≤j)

fromℕ<-cancel-< : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                  fromℕ< i<n < fromℕ< j<n → i <ℕ j
fromℕ<-cancel-< i<n j<n i<j = subst₂ _<ℕ_ (toℕ-fromℕ< i<n) (toℕ-fromℕ< j<n) i<j

------------------------------------------------------------------------
-- fromℕ<″

fromℕ<″-cong : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
               i ≡ j → fromℕ<″ i i<n ≡ fromℕ<″ j j<n
fromℕ<″-cong i<n j<n eq =
  subst₂ _≡_
    (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ i<n) i<n)
    (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ j<n) j<n)
    (fromℕ<-cong (ℕₚ.≤″⇒≤ i<n) (ℕₚ.≤″⇒≤ j<n) eq)

fromℕ<″-toℕ : ∀ {n} {i : Fin n} (toℕ<n : toℕ i ℕ.<″ n) →
                fromℕ<″ (toℕ i) toℕ<n ≡ i
fromℕ<″-toℕ {n} {i} toℕ<n = begin
  fromℕ<″ (toℕ i) _  ≡⟨ sym (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ toℕ<n) toℕ<n) ⟩
  fromℕ< _           ≡⟨ fromℕ<-toℕ i (ℕₚ.≤″⇒≤ toℕ<n) ⟩
  i ∎
  where open ≡-Reasoning

fromℕ<″-injective : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
                    fromℕ<″ i i<n ≡ fromℕ<″ j j<n → i ≡ j
fromℕ<″-injective i<n j<n eq = fromℕ<-injective (ℕₚ.≤″⇒≤ i<n) (ℕₚ.≤″⇒≤ j<n) (subst₂ _≡_
    (sym (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ i<n) i<n))
    (sym (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ j<n) j<n))
    eq)

-----------
-- Other --
-----------

suc≢zero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
suc≢zero ()

≰⇒≢ : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → m ≢ n
≰⇒≢ m≰n refl = m≰n ≤-refl

