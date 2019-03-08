open import Level using () renaming (zero to 0ℓ)
open import Data.Nat
open import Data.Nat.Properties hiding (module ≤-Reasoning; +-monoʳ-<)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₁; map₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Flip as Flip
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)

open import Algebra.FunctionProperties {A = ℕ} _≡_

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Relation.Binary
import RoutingLib.Relation.Binary.Reasoning.StrictCore as StrictReasoning
open import RoutingLib.Function.Metric.Nat

module RoutingLib.Data.Nat.Properties where

------------------------------------------------------------------------
-- Equality

ℕₛ : Setoid 0ℓ 0ℓ
ℕₛ = setoid ℕ

ℕᵈˢ : DecSetoid 0ℓ 0ℓ
ℕᵈˢ = decSetoid _≟_

abstract

  n≢1+n : ∀ n → n ≢ suc n
  n≢1+n zero    = λ()
  n≢1+n (suc n) = n≢1+n n ∘ suc-injective

------------------------------------------------------------------------
-- Ordering

suc∘pred[n]≡n : ∀ {n} → 1 ≤ n → suc (pred n) ≡ n
suc∘pred[n]≡n (s≤s z≤n) = refl

n≤suc∘pred[n] : ∀ n → n ≤ suc (pred n)
n≤suc∘pred[n] zero    = z≤n
n≤suc∘pred[n] (suc n) = s≤s ≤-refl

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
  }

≤-isDecTotalPreorder : IsDecTotalPreorder _≡_ _≤_
≤-isDecTotalPreorder = record
  { isTotalPreorder = ≤-isTotalPreorder
  ; _≟_             = _≟_
  ; _≤?_            = _≤?_
  }

≤-decTotalPreorder : DecTotalPreorder 0ℓ 0ℓ 0ℓ
≤-decTotalPreorder = record { isDecTotalPreorder = ≤-isDecTotalPreorder }

≥-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≥-decTotalOrder = Flip.decTotalOrder ≤-decTotalOrder

≤-<-isOrderingPair : IsOrderingPair _≡_ _≤_ _<_
≤-<-isOrderingPair = record
  { isEquivalence        = isEquivalence
  ; isPartialOrder       = ≤-isPartialOrder
  ; isStrictPartialOrder = <-isStrictPartialOrder
  ; <⇒≤                  = <⇒≤
  ; ≤∧≉⇒<                = ≤∧≢⇒<
  ; <-≤-trans            = <-transˡ
  ; ≤-<-trans            = <-transʳ
  }

≤-<-orderingPair : OrderingPair 0ℓ 0ℓ 0ℓ 0ℓ
≤-<-orderingPair = record { isOrderingPair = ≤-<-isOrderingPair }

abstract

  >⇒≰ : _>_ ⇒ _≰_
  >⇒≰ = <⇒≱

  ∀x≤m:n≢x⇒m<n : ∀ m n → (∀ {x} → x ≤ m → n ≢ x) → m < n
  ∀x≤m:n≢x⇒m<n _       zero    x≤m⇒n≢x = contradiction refl (x≤m⇒n≢x z≤n)
  ∀x≤m:n≢x⇒m<n zero    (suc n) x≤0⇒n≢x = s≤s z≤n
  ∀x≤m:n≢x⇒m<n (suc m) (suc n) x≤m+1⇒n≢x = s≤s (∀x≤m:n≢x⇒m<n m n (λ x≤m n≡x → x≤m+1⇒n≢x (s≤s x≤m) (cong suc n≡x)))

  ∀x<m:n≢x⇒m≤n : ∀ m n → (∀ {x} → x < m → n ≢ x) → m ≤ n
  ∀x<m:n≢x⇒m≤n zero    n       f = z≤n
  ∀x<m:n≢x⇒m≤n (suc m) zero    f = contradiction refl (f (s≤s z≤n))
  ∀x<m:n≢x⇒m≤n (suc m) (suc n) f = s≤s (∀x<m:n≢x⇒m≤n m n (λ x<m n≡x → f (s≤s x<m) (cong suc n≡x)))

  n≢0⇒0<n : ∀ {n} → n ≢ 0 → 0 < n
  n≢0⇒0<n {zero} 0≢0 = contradiction refl 0≢0
  n≢0⇒0<n {suc n} n+1≢0 = s≤s z≤n



  -- Equality reasoning

  module ≤-Reasoning where
    open StrictReasoning ≤-<-orderingPair public
      hiding (_≈⟨_⟩_)

  n<1+n : ∀ n → n < suc n
  n<1+n n = ≤-refl

  m<n⇒n≡1+o : ∀ {m n} → m < n → ∃ λ o → n ≡ suc o
  m<n⇒n≡1+o {_} {zero} ()
  m<n⇒n≡1+o {_} {suc o} m<n = o , refl

  <⇒≤suc : ∀ {x y} → x < y → x ≤ suc y
  <⇒≤suc (s≤s z≤n)       = z≤n
  <⇒≤suc (s≤s (s≤s x<y)) = s≤s (<⇒≤suc (s≤s x<y))

------------------------------------------------------------------------
-- Distance

∣-∣-identityˡ : LeftIdentity 0 ∣_-_∣
∣-∣-identityˡ x = refl

∣-∣-identityʳ : RightIdentity 0 ∣_-_∣
∣-∣-identityʳ zero    = refl
∣-∣-identityʳ (suc x) = refl

∣-∣-identity : Identity 0 ∣_-_∣
∣-∣-identity = ∣-∣-identityˡ , ∣-∣-identityʳ

m≤n+∣n-m∣ : ∀ m n → m ≤ n + ∣ n - m ∣
m≤n+∣n-m∣ zero    n       = z≤n
m≤n+∣n-m∣ (suc m) zero    = ≤-refl
m≤n+∣n-m∣ (suc m) (suc n) = s≤s (m≤n+∣n-m∣ m n)

m≤n+∣m-n∣ : ∀ m n → m ≤ n + ∣ m - n ∣
m≤n+∣m-n∣ m n = subst (m ≤_) (cong (n +_) (∣-∣-comm n m)) (m≤n+∣n-m∣ m n)

m≤∣m-n∣+n : ∀ m n → m ≤ ∣ m - n ∣ + n
m≤∣m-n∣+n m n = subst (m ≤_) (+-comm n _) (m≤n+∣m-n∣ m n)

∣-∣-triangle : ∀ x y z → ∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣
∣-∣-triangle zero    y       z       = m≤n+∣n-m∣ z y
∣-∣-triangle x       zero    z       = begin
  ∣ x - z ∣     ≤⟨ ∣n-m∣≤n⊔m x z ⟩
  x ⊔ z         ≤⟨ m⊔n≤m+n x z ⟩
  x + z         ≡⟨ cong₂ _+_ (sym (∣-∣-identityʳ x)) refl ⟩
  ∣ x - 0 ∣ + z ∎
  where open ≤-Reasoning
∣-∣-triangle x       y       zero    = begin
  ∣ x - 0 ∣             ≡⟨ ∣-∣-identityʳ x ⟩
  x                     ≤⟨ m≤∣m-n∣+n x y ⟩
  ∣ x - y ∣ + y         ≡⟨ cong₂ _+_ refl (sym (∣-∣-identityʳ y)) ⟩
  ∣ x - y ∣ + ∣ y - 0 ∣ ∎
  where open ≤-Reasoning
∣-∣-triangle (suc x) (suc y) (suc z) = ∣-∣-triangle x y z

∣-∣-isPreMetric : IsPreMetric _≡_ ∣_-_∣
∣-∣-isPreMetric = record
  { isTotalOrder    = ≤-isTotalOrder
  ; ≈-isEquivalence = isEquivalence
  ; cong            = cong₂ ∣_-_∣
  ; eq⇒0            = n≡m⇒∣n-m∣≡0
  ; 0#-minimum      = z≤n
  }

∣-∣-preMetric : PreMetric 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ
∣-∣-preMetric = record
  { isPreMetric = ∣-∣-isPreMetric
  }

∣-∣-isQuasiSemiMetric : IsQuasiSemiMetric _≡_ ∣_-_∣
∣-∣-isQuasiSemiMetric = record
  { isPreMetric = ∣-∣-isPreMetric
  ; 0⇒eq        = ∣n-m∣≡0⇒n≡m
  }

∣-∣-quasiSemiMetric : QuasiSemiMetric 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ
∣-∣-quasiSemiMetric = record
  { isQuasiSemiMetric = ∣-∣-isQuasiSemiMetric
  }

∣-∣-isSemiMetric : IsSemiMetric _≡_ ∣_-_∣
∣-∣-isSemiMetric = record
  { isQuasiSemiMetric = ∣-∣-isQuasiSemiMetric
  ; sym               = ∣-∣-comm
  }

∣-∣-semiMetric : SemiMetric 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ
∣-∣-semiMetric = record
  { isSemiMetric = ∣-∣-isSemiMetric
  }

∣-∣-isMetric : IsMetric _≡_ ∣_-_∣
∣-∣-isMetric = record
  { isSemiMetric = ∣-∣-isSemiMetric
  ; triangle     = ∣-∣-triangle
  }

∣-∣-metric : Metric 0ℓ 0ℓ
∣-∣-metric = record
  { isMetric = ∣-∣-isMetric
  }

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

a≤b*a : ∀ a b → a ≤ suc b * a
a≤b*a a b = m≤m+n _ _

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


m≤n⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesˡ (m ≤_)
m≤n⇒m≤n⊔o o m≤n = ≤-trans m≤n (m≤m⊔n _ o)

m≤o⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesʳ (m ≤_)
m≤o⇒m≤n⊔o n m≤o = ≤-trans m≤o (n≤m⊔n n _)

m≤n⊎m≤o⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesᵒ (m ≤_)
m≤n⊎m≤o⇒m≤n⊔o _ o (inj₁ m≤n) = m≤n⇒m≤n⊔o o m≤n
m≤n⊎m≤o⇒m≤n⊔o n _ (inj₂ m≤o) = m≤o⇒m≤n⊔o n m≤o

m<n⊎m<o⇒m<n⊔o : ∀ {m} → _⊔_ Preservesᵒ (m <_)
m<n⊎m<o⇒m<n⊔o n o m<n⊎m<o = m≤n⊎m≤o⇒m≤n⊔o n o m<n⊎m<o

m≤n×m≤o⇒m≤n⊔o : ∀ {m} → _⊔_ Preservesᵇ (m ≤_)
m≤n×m≤o⇒m≤n⊔o m≤n _ = m≤n⇒m≤n⊔o _ m≤n

n≤m×o≤m⇒n⊔o≤m : ∀ {m} → _⊔_ Preservesᵇ (_≤ m)
n≤m×o≤m⇒n⊔o≤m n≤m o≤m = subst (_ ≤_) (⊔-idem _) (⊔-mono-≤ n≤m o≤m)


n⊔o≤m⇒n≤m : ∀ {m} → _⊔_ Forcesˡ (_≤ m)
n⊔o≤m⇒n≤m n o n⊔o≤m = ≤-trans (m≤m⊔n n o) n⊔o≤m

n⊔o≤m⇒o≤m : ∀ {m} → _⊔_ Forcesʳ (_≤ m)
n⊔o≤m⇒o≤m n o n⊔o≤m = ≤-trans (n≤m⊔n n o) n⊔o≤m

n⊔o≤m⇒n≤m×o≤m : ∀ {m} → _⊔_ Forcesᵇ (_≤ m)
n⊔o≤m⇒n≤m×o≤m n o n⊔o≤m = n⊔o≤m⇒n≤m n o n⊔o≤m , n⊔o≤m⇒o≤m n o n⊔o≤m

n⊔o≤m⇒n≤m⊎o≤m : ∀ {m} → _⊔_ Forcesᵒ (_≤ m)
n⊔o≤m⇒n≤m⊎o≤m n o n⊔o≤m = inj₁ (n⊔o≤m⇒n≤m n o n⊔o≤m)


-- _⊓_ and _≤_


m⊔n≤o⇒m≤o : ∀ {m n o} → m ⊔ n ≤ o → m ≤ o
m⊔n≤o⇒m≤o m⊔n≤o = ≤-trans (m≤m⊔n _ _) m⊔n≤o

m⊔n≤o⇒n≤o : ∀ {m n o} → m ⊔ n ≤ o → n ≤ o
m⊔n≤o⇒n≤o m⊔n≤o = ≤-trans (n≤m⊔n _ _) m⊔n≤o

n≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesˡ (_≤ m)
n≤m⇒n⊓o≤m o m≤n = ≤-trans (m⊓n≤m _ o) m≤n

o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesʳ (_≤ m)
o≤m⇒n⊓o≤m n o≤m = ≤-trans (m⊓n≤n n _) o≤m

n≤m⊎o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesᵒ (_≤ m)
n≤m⊎o≤m⇒n⊓o≤m _ o (inj₁ n≤m) = n≤m⇒n⊓o≤m o n≤m
n≤m⊎o≤m⇒n⊓o≤m n _ (inj₂ o≤m) = o≤m⇒n⊓o≤m n o≤m

n≤m×o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesᵇ (_≤ m)
n≤m×o≤m⇒n⊓o≤m n≤m o≤m = n≤m⇒n⊓o≤m _ n≤m

m≤n×m≤o⇒m≤n⊓o : ∀ {m} → _⊓_ Preservesᵇ (m ≤_)
m≤n×m≤o⇒m≤n⊓o m≤n m≤o = subst (_≤ _) (⊓-idem _) (⊓-mono-≤ m≤n m≤o)


m≤n⊓o⇒m≤n : ∀ {m} → _⊓_ Forcesˡ (m ≤_)
m≤n⊓o⇒m≤n n o m≤n⊓o = ≤-trans m≤n⊓o (m⊓n≤m n o)

m≤n⊓o⇒m≤o : ∀ {m} → _⊓_ Forcesʳ (m ≤_)
m≤n⊓o⇒m≤o n o m≤n⊓o = ≤-trans m≤n⊓o (m⊓n≤n n o)

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
m+[n∸o]≤[m+n]∸o m zero    (suc o) = n∸m≤n (suc o) (m + 0)
m+[n∸o]≤[m+n]∸o m (suc n) (suc o) = begin
  (m + suc n) ∸ suc o ≡⟨ cong (_∸ suc o) (+-suc m n) ⟩
  (suc m + n) ∸ suc o ≡⟨⟩
  (m + n) ∸ o         ≤⟨ m+[n∸o]≤[m+n]∸o m n o ⟩
  m + (n ∸ o)         ∎
  where open ≤-Reasoning

∸-monoʳ-< : ∀ {m n o} → o < n → n ≤ m → m ∸ n < m ∸ o
∸-monoʳ-< {_} {suc n} {zero}  (s≤s o<n) (s≤s n<m) = s≤s (n∸m≤n n _)
∸-monoʳ-< {_} {suc n} {suc o} (s≤s o<n) (s≤s n<m) = ∸-monoʳ-< o<n n<m

m>n⇒m∸n≢0 : ∀ {m n} → m > n → m ∸ n ≢ 0
m>n⇒m∸n≢0 {n = zero}  (s≤s m>n) = λ()
m>n⇒m∸n≢0 {n = suc n} (s≤s m>n) = m>n⇒m∸n≢0 m>n

n∸1+m<n : ∀ m {n} → 1 ≤ n → n ∸ suc m < n
n∸1+m<n m (s≤s z≤n) = s≤s (n∸m≤n m _)

m<n⇒0<n∸m : ∀ {m n} → m < n → 0 < n ∸ m
m<n⇒0<n∸m {_}     {zero}  ()
m<n⇒0<n∸m {zero}  {suc n} _         = s≤s z≤n
m<n⇒0<n∸m {suc m} {suc n} (s≤s m<n) = m<n⇒0<n∸m m<n

m<n⇒n∸m≡1+o : ∀ {m n} → m < n → ∃ λ o → n ∸ m ≡ suc o
m<n⇒n∸m≡1+o {_}     {zero}  ()
m<n⇒n∸m≡1+o {zero}  {suc n} (s≤s m<n) = n , refl
m<n⇒n∸m≡1+o {suc m} {suc n} (s≤s m<n) = m<n⇒n∸m≡1+o m<n

∸-cancelˡ-≡ :  ∀ {x y z} → y ≤ x → z ≤ x → x ∸ y ≡ x ∸ z → y ≡ z
∸-cancelˡ-≡ {_} {_}     {_}     z≤n       z≤n       _       = refl
∸-cancelˡ-≡ {_} {_}     {suc z} z≤n       (s≤s z≤x) 1+x≡x∸z = contradiction (sym 1+x≡x∸z) (<⇒≢ (s≤s (n∸m≤n z _)))
∸-cancelˡ-≡ {_} {suc y} {_}     (s≤s y≤x) z≤n       x∸y≡1+x = contradiction x∸y≡1+x (<⇒≢ (s≤s (n∸m≤n y _)))
∸-cancelˡ-≡ {_} {_}     {_}     (s≤s y≤x) (s≤s z≤x) x∸y≡x∸z = cong suc (∸-cancelˡ-≡ y≤x z≤x x∸y≡x∸z)

∸-cancelʳ-≤ : ∀ {m n o} → m ≤ o → o ∸ n ≤ o ∸ m → m ≤ n
∸-cancelʳ-≤ {zero}  {_}     {_}     _         _       = z≤n
∸-cancelʳ-≤ {suc m} {_}     {zero}  ()
∸-cancelʳ-≤ {suc m} {zero}  {suc o} n≤o       o+1≤o∸m = contradiction (≤-trans o+1≤o∸m (n∸m≤n m o)) 1+n≰n
∸-cancelʳ-≤ {_}     {suc n} {_}     (s≤s m≤o) o∸n≤o∸m = s≤s (∸-cancelʳ-≤ m≤o o∸n≤o∸m)

∸-cancelʳ-< : ∀ {m n o} → o ∸ m < o ∸ n → n < m
∸-cancelʳ-< {zero}  {n}     {o}    o<o∸n   = contradiction o<o∸n (m≮m∸n o n)
∸-cancelʳ-< {suc m} {zero}  {_}    o∸n<o∸m = s≤s z≤n
∸-cancelʳ-< {suc m} {suc n} {zero} ()
∸-cancelʳ-< {suc m} {suc n} {suc o} o∸n<o∸m = s≤s (∸-cancelʳ-< o∸n<o∸m)
