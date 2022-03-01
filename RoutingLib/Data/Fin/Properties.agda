
module RoutingLib.Data.Fin.Properties where

open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
open import Data.Product using (_,_)
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s; zero; suc)
  renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans; subst₂; module ≡-Reasoning)
import Function.Bijection as Bijection

𝔽ₛ : ℕ → Setoid _ _
𝔽ₛ = ≡-setoid

private
  variable
    m n : ℕ

lower : ∀ {m n} (i : Fin m) → .(toℕ i <ℕ n) → Fin n
lower {suc _} {suc n} fzero    leq = fzero
lower {suc _} {suc n} (fsuc i) leq = fsuc (lower i (ℕₚ.≤-pred leq))

lower-injective : ∀ {m n} (i j : Fin m) (i<n : toℕ i <ℕ n) (j<n : toℕ j <ℕ n)  →
                  lower i i<n ≡ lower j j<n → i ≡ j
lower-injective {suc _} {suc n} fzero    fzero    i<n       j<n       eq = refl
lower-injective {suc _} {suc n} (fsuc i) (fsuc j) (s≤s i<n) (s≤s j<n) eq =
  cong fsuc (lower-injective i j i<n j<n (suc-injective eq))

------------------------------------------------------------------------
-- fromℕ<

fromℕ<-mono-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                 i ≤ℕ j → fromℕ< i<n ≤ fromℕ< j<n
fromℕ<-mono-≤ (s≤s z≤n)       (s≤s _)         z≤n       = z≤n
fromℕ<-mono-≤ (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) (s≤s i≤j) =
  s≤s (fromℕ<-mono-≤ (s≤s i<n) (s≤s j<n) i≤j)

fromℕ<-cancel-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                  fromℕ< i<n ≤ fromℕ< j<n → i ≤ℕ j
fromℕ<-cancel-≤ i<n j<n = subst₂ _≤ℕ_ (toℕ-fromℕ< i<n) (toℕ-fromℕ< j<n)

fromℕ<-cancel-< : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                  fromℕ< i<n < fromℕ< j<n → i <ℕ j
fromℕ<-cancel-< i<n j<n = subst₂ _<ℕ_ (toℕ-fromℕ< i<n) (toℕ-fromℕ< j<n)

fromℕ<-irrelevant : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                    i ≡ j → fromℕ< i<n ≡ fromℕ< j<n
fromℕ<-irrelevant i<n j<n refl = cong fromℕ< (ℕₚ.<-irrelevant i<n j<n)

------------------------------------------------------------------------
-- fromℕ<″

fromℕ<″-cong : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
               i ≡ j → fromℕ<″ i i<n ≡ fromℕ<″ j j<n
fromℕ<″-cong i<n j<n eq =
  subst₂ _≡_
    (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ i<n) i<n)
    (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ j<n) j<n)
    (fromℕ<-irrelevant (ℕₚ.≤″⇒≤ i<n) (ℕₚ.≤″⇒≤ j<n) eq)

fromℕ<″-toℕ : ∀ {n} {i : Fin n} (toℕ<n : toℕ i ℕ.<″ n) →
                fromℕ<″ (toℕ i) toℕ<n ≡ i
fromℕ<″-toℕ {n} {i} toℕ<n = begin
  fromℕ<″ (toℕ i) _  ≡⟨ sym (fromℕ<≡fromℕ<″ (ℕₚ.≤″⇒≤ toℕ<n) toℕ<n) ⟩
  fromℕ< _           ≡⟨ fromℕ<-toℕ i (ℕₚ.≤″⇒≤ toℕ<n) ⟩
  i ∎
  where open ≡-Reasoning

fromℕ<″-injective : ∀ {n i j} (i<n : i ℕ.<″ n) (j<n : j ℕ.<″ n) →
                    fromℕ<″ i i<n ≡ fromℕ<″ j j<n → i ≡ j
fromℕ<″-injective i<n j<n eq = fromℕ<-injective _ _ (ℕₚ.≤″⇒≤ i<n) (ℕₚ.≤″⇒≤ j<n) (subst₂ _≡_
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

≰⇒> : ∀ {n} {i j : Fin n} → ¬ (i ≤ j) → j < i
≰⇒> = ℕₚ.≰⇒>

i<j⇒j≢0 : ∀ {n} {i j : Fin (suc n)} → i < j → j ≢ fzero
i<j⇒j≢0 {j = fsuc j} i<j ()

i≰j⇒i≢0 : ∀ {n} {i j : Fin (suc n)} → ¬ (i ≤ j) → i ≢ fzero
i≰j⇒i≢0 i≰j = i<j⇒j≢0 (≰⇒> i≰j)

≤-pred : ∀ {n} (i : Fin n) → pred i ≤ i
≤-pred fzero    = z≤n
≤-pred (fsuc i) = ℕₚ.≤-step (ℕₚ.≤-reflexive (toℕ-inject₁ i))

cast-injective : ∀ {m n} (m≡n : m ≡ n) {i j : Fin m} → cast m≡n i ≡ cast m≡n j → i ≡ j
cast-injective {suc m} {suc n} m≡n {fzero}  {fzero} eq  = refl
cast-injective {suc m} {suc n} m≡n {fsuc i} {fsuc j} eq =
  cong fsuc (cast-injective (ℕₚ.suc-injective m≡n) (suc-injective eq))

suc-pred : ∀ {i : Fin (suc n)} → i ≢ fzero → toℕ (fsuc (pred i)) ≡ toℕ i
suc-pred {i = fzero}  i≢0 = contradiction refl i≢0
suc-pred {i = fsuc i} i≢0 = cong suc (toℕ-inject₁ i)
