open import Level using (0ℓ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₁; map₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Flip as Flip
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Algebra.Definitions

module RoutingLib.Data.Nat.Properties where

------------------------------------------------------------------------
-- Equality

ℕₛ : Setoid 0ℓ 0ℓ
ℕₛ = setoid ℕ

ℕᵈˢ : DecSetoid 0ℓ 0ℓ
ℕᵈˢ = decSetoid _≟_

------------------------------------------------------------------------
-- Ordering

suc∘pred[n]≡n : ∀ {n} → 1 ≤ n → suc (pred n) ≡ n
suc∘pred[n]≡n (s≤s z≤n) = refl

n≤suc∘pred[n] : ∀ n → n ≤ suc (pred n)
n≤suc∘pred[n] zero    = z≤n
n≤suc∘pred[n] (suc n) = s≤s ≤-refl

≥-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≥-decTotalOrder = Flip.decTotalOrder ≤-decTotalOrder

-- Equality reasoning

m<n⇒n≡1+o : ∀ {m n} → m < n → ∃ λ o → n ≡ suc o
m<n⇒n≡1+o {_} {zero} ()
m<n⇒n≡1+o {_} {suc o} m<n = o , refl

<⇒≤suc : ∀ {x y} → x < y → x ≤ suc y
<⇒≤suc (s≤s z≤n)       = z≤n
<⇒≤suc (s≤s (s≤s x<y)) = s≤s (<⇒≤suc (s≤s x<y))

------------------------------------------------------------------------
-- Addition and multiplication

m≤n⇒m+o≡n : ∀ {m n} → m ≤ n → ∃ λ o → m + o ≡ n
m≤n⇒m+o≡n {_} {n} z≤n = n , refl
m≤n⇒m+o≡n (s≤s m≤n) with m≤n⇒m+o≡n m≤n
... | o , m+o≡n = o , cong suc m+o≡n

m≤n⇒o+m≡n : ∀ {m n} → m ≤ n → ∃ λ o → o + m ≡ n
m≤n⇒o+m≡n {m} m≤n = map₂ (λ { refl → +-comm _ m }) (m≤n⇒m+o≡n m≤n)

m<n⇒1+m+o≡n : ∀ {m n} → m < n → ∃ λ o → suc m + o ≡ n
m<n⇒1+m+o≡n {_} {suc n} (s≤s z≤n) = n , refl
m<n⇒1+m+o≡n (s≤s (s≤s m<n)) with m<n⇒1+m+o≡n (s≤s m<n)
... | o , m+o+1≡n = o , (cong suc m+o+1≡n)


------------------------------------------------------------------------
-- Min and max

-- _⊔_ and _≡_

⊔-preserves-≡x : ∀ {x} → _⊔_ Preservesᵇ (_≡ x)
⊔-preserves-≡x refl refl = ⊔-idem _

⊔-preserves-x≡ : ∀ {x} → _⊔_ Preservesᵇ (x ≡_)
⊔-preserves-x≡ refl refl = sym (⊔-idem _)


-- _⊓_ and _≡_

⊓-preserves-≡x : ∀ {x} → _⊓_ Preservesᵇ (_≡ x)
⊓-preserves-≡x refl refl = ⊓-idem _

⊓-preserves-x≡ : ∀ {x} → _⊓_ Preservesᵇ (x ≡_)
⊓-preserves-x≡ refl refl = sym (⊓-idem _)

-- _⊔_ and _≤_

m≤n⊎m≤o⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesᵒ (m ≤_)
m≤n⊎m≤o⇒m≤n⊔o _ o (inj₁ m≤n) = m≤n⇒m≤n⊔o o m≤n
m≤n⊎m≤o⇒m≤n⊔o n _ (inj₂ m≤o) = m≤n⇒m≤o⊔n n m≤o

m<n⊎m<o⇒m<n⊔o : ∀ {m} → _⊔_ Preservesᵒ (m <_)
m<n⊎m<o⇒m<n⊔o n o m<n⊎m<o = m≤n⊎m≤o⇒m≤n⊔o n o m<n⊎m<o

m≤n×m≤o⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesᵇ (m ≤_)
m≤n×m≤o⇒m≤n⊔o m≤n _ = m≤n⇒m≤n⊔o _ m≤n

n≤m×o≤m⇒n⊔o≤m : ∀ {m} → _⊔_ Preservesᵇ (_≤ m)
n≤m×o≤m⇒n⊔o≤m n≤m o≤m = subst (_ ≤_) (⊔-idem _) (⊔-mono-≤ n≤m o≤m)

n⊔o≤m⇒n≤m×o≤m : ∀ {m} → _⊔_ Forcesᵇ (_≤ m)
n⊔o≤m⇒n≤m×o≤m n o n⊔o≤m = m⊔n≤o⇒m≤o n o n⊔o≤m , m⊔n≤o⇒n≤o n o n⊔o≤m

n⊔o≤m⇒n≤m⊎o≤m : ∀ {m} → _⊔_ Forcesᵒ (_≤ m)
n⊔o≤m⇒n≤m⊎o≤m n o n⊔o≤m = inj₁ (m⊔n≤o⇒m≤o n o n⊔o≤m)


-- _⊓_ and _≤_

n≤m⊎o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesᵒ (_≤ m)
n≤m⊎o≤m⇒n⊓o≤m _ o (inj₁ n≤m) = m≤n⇒m⊓o≤n o n≤m
n≤m⊎o≤m⇒n⊓o≤m n _ (inj₂ o≤m) = m≤n⇒o⊓m≤n n o≤m

n≤m×o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesᵇ (_≤ m)
n≤m×o≤m⇒n⊓o≤m n≤m o≤m = m≤n⇒m⊓o≤n _ n≤m

m≤n×m≤o⇒m≤n⊓o : ∀ {m} → _⊓_ Preservesᵇ (m ≤_)
m≤n×m≤o⇒m≤n⊓o m≤n m≤o = subst (_≤ _) (⊓-idem _) (⊓-mono-≤ m≤n m≤o)


m≤n⊓o⇒m≤n×m≤o : ∀ {m} → _⊓_ Forcesᵇ (m ≤_)
m≤n⊓o⇒m≤n×m≤o n o m≤n⊓o = m≤n⊓o⇒m≤n n o m≤n⊓o , m≤n⊓o⇒m≤o n o m≤n⊓o

m≤n⊓o⇒m≤n⊎m≤o : ∀ {m} → _⊓_ Forcesᵒ (m ≤_)
m≤n⊓o⇒m≤n⊎m≤o n o m≤n⊓o = inj₁ (m≤n⊓o⇒m≤n n o m≤n⊓o)


n<m⇒n⊓o<m : ∀ {m} → _⊓_ Preservesˡ (_< m)
n<m⇒n⊓o<m o n<m = ≤-trans (s≤s (m⊓n≤m _ o)) n<m

o<m⇒n⊓o<m : ∀ {m} → _⊓_ Preservesʳ (_< m)
o<m⇒n⊓o<m n o<m = ≤-trans (s≤s (m⊓n≤n n _)) o<m

n<m⊎o<m⇒n⊓o<m : ∀ {m} → _⊓_ Preservesᵒ (_< m)
n<m⊎o<m⇒n⊓o<m n o (inj₁ n<m) = n<m⇒n⊓o<m o n<m
n<m⊎o<m⇒n⊓o<m n o (inj₂ o<m) = o<m⇒n⊓o<m n o<m

m<n×m<o⇒m<n⊓o : ∀ {m} → _⊓_ Preservesᵇ (m <_)
m<n×m<o⇒m<n⊓o m<n m<o = subst (_< _) (⊓-idem _) (⊓-mono-< m<n m<o)

------------------------------------------------------------------------
-- Subtraction

m+[n∸o]≤[m+n]∸o : ∀ m n o → (m + n) ∸ o ≤ m + (n ∸ o)
m+[n∸o]≤[m+n]∸o m n       zero    = ≤-refl
m+[n∸o]≤[m+n]∸o m zero    (suc o) = m∸n≤m (m + 0) (suc o)
m+[n∸o]≤[m+n]∸o m (suc n) (suc o) = begin
  (m + suc n) ∸ suc o ≡⟨ cong (_∸ suc o) (+-suc m n) ⟩
  (suc m + n) ∸ suc o ≡⟨⟩
  (m + n) ∸ o         ≤⟨ m+[n∸o]≤[m+n]∸o m n o ⟩
  m + (n ∸ o)         ∎
  where open ≤-Reasoning

n∸[1+m]<n : ∀ m {n} → 1 ≤ n → n ∸ suc m < n
n∸[1+m]<n m (s≤s z≤n) = s≤s (m∸n≤m _ m)

m<n⇒n∸m≡1+o : ∀ {m n} → m < n → ∃ λ o → n ∸ m ≡ suc o
m<n⇒n∸m≡1+o {zero}  {suc n} (s≤s m<n) = n , refl
m<n⇒n∸m≡1+o {suc m} {suc n} (s≤s m<n) = m<n⇒n∸m≡1+o m<n
