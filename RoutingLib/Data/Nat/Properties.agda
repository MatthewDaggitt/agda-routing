open import Level using () renaming (zero to lzero)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple using (+-comm; +-suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₁)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)
open import Algebra
open import Algebra.FunctionProperties (_≡_ {A = ℕ}) using (Idempotent; RightIdentity; RightZero; Selective; _DistributesOverʳ_; _DistributesOverˡ_; _DistributesOver_)

open import RoutingLib.Algebra.FunctionProperties using (_×-Preserves_; _⊎-Preservesₗ_; _⊎-Preservesᵣ_; _⊎-Preserves_; _Forces-×_; _Forces-⊎_; RightCancellative; LeftCancellative)


module RoutingLib.Data.Nat.Properties where

  open import Data.Nat.Properties.Simple public

  --------------
  -- Equality --
  --------------

  ℕₛ : Setoid lzero lzero
  ℕₛ = setoid ℕ

  ℕᵈˢ : DecSetoid lzero lzero
  ℕᵈˢ = decSetoid _≟_
  
  abstract

    -- stdlib
    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    n≢1+n : ∀ n → n ≢ suc n
    n≢1+n zero    = λ()
    n≢1+n (suc n) = n≢1+n n ∘ suc-injective

    --------------
    -- Ordering --
    --------------

    -- stdlib
    infix 4 _<?_
    _<?_ : Decidable _<_
    x <? y = suc x ≤? y
    
    -- stdlib
    open Relation.Binary.DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans; total to ≤-total; antisym to ≤-antisym; totalOrder to ≤-totalOrder) public

    -- stdlib
    <-cmp : Trichotomous _≡_ _<_
    <-cmp zero    zero    = tri≈ (λ())     refl  (λ())
    <-cmp zero    (suc n) = tri< (s≤s z≤n) (λ()) (λ())
    <-cmp (suc m) zero    = tri> (λ())     (λ()) (s≤s z≤n)
    <-cmp (suc m) (suc n) with <-cmp m n
    ... | tri< m≤n m≢n n≰m = tri< (s≤s m≤n)      (m≢n ∘ suc-injective) (n≰m ∘ ≤-pred)
    ... | tri≈ m≰n m≡n n≰m = tri≈ (m≰n ∘ ≤-pred) (cong suc m≡n)        (n≰m ∘ ≤-pred)
    ... | tri> m≰n m≢n n≤m = tri> (m≰n ∘ ≤-pred) (m≢n ∘ suc-injective) (s≤s n≤m)

    -- stdlib
    <-irrefl : Irreflexive _≡_ _<_
    <-irrefl refl (s≤s n<n) = <-irrefl refl n<n

    -- stdlib
    <-asym : Asymmetric _<_
    <-asym (s≤s n<m) (s≤s m<n) = <-asym n<m m<n

    -- stdlib
    <-transᵣ : Trans _≤_ _<_ _<_
    <-transᵣ m≤n (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

    -- stdlib
    <-transₗ : Trans _<_ _≤_ _<_
    <-transₗ (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)


    -- stdlib
    open DistributiveLattice Data.Nat.Properties.distributiveLattice using () renaming (∨-comm to ⊓-comm; ∨-assoc to ⊓-assoc; ∧-comm to ⊔-comm) public

    -- stdlib
    0-idᵣ-⊔ : RightIdentity zero _⊔_
    0-idᵣ-⊔ zero = refl
    0-idᵣ-⊔ (suc x) = refl

    -- stdlib
    0-zeᵣ-⊓ : RightZero zero _⊓_
    0-zeᵣ-⊓ zero = refl
    0-zeᵣ-⊓ (suc x) = refl
    
    -- stdlib
    ⊓-idem : Idempotent _⊓_
    ⊓-idem x with ⊓-sel x x
    ... | inj₁ x⊓x≈x = x⊓x≈x
    ... | inj₂ x⊓x≈x = x⊓x≈x

    -- stdlib
    ⊔-idem : Idempotent _⊔_
    ⊔-idem x with ⊔-sel x x
    ... | inj₁ x⊔x≈x = x⊔x≈x
    ... | inj₂ x⊔x≈x = x⊔x≈x

    



  abstract

   

    ≤-stepsᵣ : ∀ {m n} k → m ≤ n → m ≤ n + k
    ≤-stepsᵣ {m} {n} k m≤n = subst (m ≤_) (+-comm k n) (≤-steps k m≤n)

    ≤⇒≯ : _≤_ ⇒ _≯_
    ≤⇒≯ z≤n       ()
    ≤⇒≯ (s≤s m≤n) (s≤s n≤m) = ≤⇒≯ m≤n n≤m

    -- stdlib
    <⇒≤ : _<_ ⇒ _≤_
    <⇒≤ (s≤s m≤n) = ≤-trans m≤n (≤-step ≤-refl)

    -- stdlib  
    <⇒≢ : _<_ ⇒ _≢_
    <⇒≢ m<n refl = 1+n≰n m<n

    -- stdlib
    <⇒≱ : _<_ ⇒ _≱_
    <⇒≱ (s≤s m+1≤n) (s≤s n≤m) = <⇒≱ m+1≤n n≤m

    -- stdlib
    <⇒≯ : _<_ ⇒ _≯_
    <⇒≯ (s≤s p<q) (s≤s q<p) = <⇒≯ p<q q<p

    >⇒≰ : _>_ ⇒ _≰_
    >⇒≰ = <⇒≱

    
    -- stdlib
    ≮⇒≥ : _≮_ ⇒ _≥_
    ≮⇒≥ {_}     {zero}  _       = z≤n
    ≮⇒≥ {zero}  {suc j} 1≮j+1   = contradiction (s≤s z≤n) 1≮j+1
    ≮⇒≥ {suc i} {suc j} i+1≮j+1 = s≤s (≮⇒≥ (i+1≮j+1 ∘ s≤s))

    -- stdlib
    ≰⇒≥ : _≰_ ⇒ _≥_
    ≰⇒≥ {_}     {zero}  _       = z≤n
    ≰⇒≥ {zero}  {suc j} 0≰j+1   = contradiction z≤n 0≰j+1
    ≰⇒≥ {suc i} {suc j} i+1≰j+1 = s≤s (≰⇒≥ (i+1≰j+1 ∘ s≤s))

    -- stdlib
    ≤+≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
    ≤+≢⇒< {zero} {zero} m≤n m≢n = contradiction refl m≢n
    ≤+≢⇒< {zero} {suc n} m≤n m≢n = s≤s z≤n
    ≤+≢⇒< {suc m} {zero} ()
    ≤+≢⇒< {suc m} {suc n} (s≤s m≤n) 1+m≢1+n = s≤s (≤+≢⇒< m≤n (1+m≢1+n ∘ cong suc))

    ≤-cardinality : ∀ {m n} (≤₁ : m ≤ n) (≤₂ : m ≤ n) → ≤₁ ≡ ≤₂
    ≤-cardinality z≤n      z≤n      = refl
    ≤-cardinality (s≤s ≤₁) (s≤s ≤₂) = cong s≤s (≤-cardinality ≤₁ ≤₂)

    ∀x≤m:n≢x⇒m<n : ∀ m n → (∀ {x} → x ≤ m → n ≢ x) → m < n
    ∀x≤m:n≢x⇒m<n _ zero    x≤m⇒n≢x = contradiction refl (x≤m⇒n≢x z≤n)
    ∀x≤m:n≢x⇒m<n zero (suc n) x≤0⇒n≢x = s≤s z≤n
    ∀x≤m:n≢x⇒m<n (suc m) (suc n) x≤m+1⇒n≢x = s≤s (∀x≤m:n≢x⇒m<n m n (λ x≤m n≡x → x≤m+1⇒n≢x (s≤s x≤m) (cong suc n≡x)))

    n≢0⇒0<n : ∀ {n} → n ≢ 0 → 0 < n
    n≢0⇒0<n {zero} 0≢0 = contradiction refl 0≢0
    n≢0⇒0<n {suc n} n+1≢0 = s≤s z≤n

    m<n⇒n≢0 : ∀ {m n} → m < n → n ≢ 0
    m<n⇒n≢0 (s≤s m≤n) ()
    
    n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
    n≤0⇒n≡0 z≤n = refl

    n≮n : ∀ n → n ≮ n
    n≮n n = <-irrefl (refl {x = n})

    n<1+n : ∀ n → n < suc n
    n<1+n n = ≤-refl
    
    m<n⇒n≡1+o : ∀ {m n} → m < n → ∃ λ o → n ≡ suc o
    m<n⇒n≡1+o {_} {zero} ()
    m<n⇒n≡1+o {_} {suc o} m<n = o , refl

    
    ---------------------------------
    -- Addition and multiplication --
    ---------------------------------

    -- std-lib
    +-monoˡ-< : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
    +-monoˡ-< {_} {suc y} (s≤s z≤n)       u≤v = s≤s (≤-steps y u≤v)
    +-monoˡ-< {_} {_}     (s≤s (s≤s x<y)) u≤v = s≤s (+-monoˡ-< (s≤s x<y) u≤v)

    -- std-lib
    +-monoʳ-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
    +-monoʳ-< {x} {y} {u} {v} x≤y u<v rewrite +-comm x u | +-comm y v = +-monoˡ-< u<v x≤y

    -- std-lib
    +-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
    +-mono-< x≤y = +-monoʳ-< (<⇒≤ x≤y)
    
    -- std-lib
    cancel-+-right : RightCancellative _≡_ _+_
    cancel-+-right {m} {n} o m+o≡n+o = cancel-+-left o (trans (+-comm o m) (trans m+o≡n+o (+-comm n o)))

    m≤n⇒m+o≡n : ∀ {m n} → m ≤ n → ∃ λ o → m + o ≡ n
    m≤n⇒m+o≡n {_} {n} z≤n = n , refl
    m≤n⇒m+o≡n (s≤s m≤n) with m≤n⇒m+o≡n m≤n
    ... | o , m+o≡n = o , cong suc m+o≡n

    m<n⇒1+m+o≡n : ∀ {m n} → m < n → ∃ λ o → suc m + o ≡ n
    m<n⇒1+m+o≡n {_} {suc n} (s≤s z≤n) = n , refl
    m<n⇒1+m+o≡n (s≤s (s≤s m<n)) with m<n⇒1+m+o≡n (s≤s m<n)
    ... | o , m+o+1≡n = o , (cong suc m+o+1≡n)

    -- stdlib
    m+n≤o⇒n≤o : ∀ m {n o} → m + n ≤ o → n ≤ o
    m+n≤o⇒n≤o zero    n≤o   = n≤o
    m+n≤o⇒n≤o (suc m) m+n<o = m+n≤o⇒n≤o m (<⇒≤ m+n<o)

    -- stdlib
    m+n≮n : ∀ m n → m + n ≮ n
    m+n≮n zero    n                   = <-irrefl refl
    m+n≮n (suc m) (suc n) (s≤s m+n<n) = m+n≮n m (suc n) (≤-step m+n<n)


    -----------------
    -- Min and max --
    -----------------

    -- stdlib
    m⊓n≤n : ∀ m n → m ⊓ n ≤ n
    m⊓n≤n m n = subst (_≤ n) (⊓-comm n m) (m⊓n≤m n m)

    -- stdlib
    n≤m⊔n : ∀ m n → n ≤ m ⊔ n
    n≤m⊔n m n = subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)


    -- stdlib
    ⊔-mono-≤ : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
    ⊔-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊔-sel x u
    ... | inj₁ x⊔u≡x rewrite x⊔u≡x = ≤-trans x≤y (m≤m⊔n y v)
    ... | inj₂ x⊔u≡u rewrite x⊔u≡u = ≤-trans u≤v (n≤m⊔n y v)

    -- std-lib
    ⊔-mono-< : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
    ⊔-mono-< = ⊔-mono-≤

    -- stdlib
    ⊓-mono-≤ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
    ⊓-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊓-sel y v
    ... | inj₁ y⊓v≡y rewrite y⊓v≡y = ≤-trans (m⊓n≤m x u) x≤y
    ... | inj₂ y⊓v≡v rewrite y⊓v≡v = ≤-trans (m⊓n≤n x u) u≤v

    ⊓-monoˡ-≤ : ∀ n → (_⊓ n) Preserves _≤_ ⟶ _≤_
    ⊓-monoˡ-≤ n m≤o = ⊓-mono-≤ m≤o ≤-refl

    ⊓-monoʳ-≤ : ∀ n → (n ⊓_) Preserves _≤_ ⟶ _≤_
    ⊓-monoʳ-≤ n m≤o = ⊓-mono-≤ (≤-refl {n}) m≤o

    -- stdlib
    ⊓-mono-< : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
    ⊓-mono-< = ⊓-mono-≤


    m≤n⇒m⊓n≡m : ∀ {m n} → m ≤ n → m ⊓ n ≡ m
    m≤n⇒m⊓n≡m z≤n       = refl
    m≤n⇒m⊓n≡m (s≤s m≤n) = cong suc (m≤n⇒m⊓n≡m m≤n)

    n≤m⇒m⊓n≡n : ∀ {m n} → n ≤ m → m ⊓ n ≡ n
    n≤m⇒m⊓n≡n {m} n≤m = trans (⊓-comm m _) (m≤n⇒m⊓n≡m n≤m)
    
    n≤m⇒m⊔n≡m : ∀ {m n} → n ≤ m → m ⊔ n ≡ m
    n≤m⇒m⊔n≡m z≤n       = 0-idᵣ-⊔ _
    n≤m⇒m⊔n≡m (s≤s n≤m) = cong suc (n≤m⇒m⊔n≡m n≤m)

    m≤n⇒m⊔n≡n : ∀ {m n} → m ≤ n → m ⊔ n ≡ n
    m≤n⇒m⊔n≡n {m} m≤n = trans (⊔-comm m _) (n≤m⇒m⊔n≡m m≤n)


    m⊔n≡m⇒n≤m : ∀ {m n} → m ⊔ n ≡ m → n ≤ m
    m⊔n≡m⇒n≤m {m} {n} m⊔n≡m rewrite sym m⊔n≡m = n≤m⊔n m n

    n⊔m≡m⇒n≤m : ∀ {m n} → n ⊔ m ≡ m → n ≤ m
    n⊔m≡m⇒n≤m n⊔m≡m = subst (_ ≤_) n⊔m≡m (m≤m⊔n _ _)

    m⊓n≡n⇒n≤m : ∀ {m n} → m ⊓ n ≡ n → n ≤ m
    m⊓n≡n⇒n≤m m⊓n≡n = subst (_≤ _) m⊓n≡n (m⊓n≤m _ _)


    m⊔n≤o⇒m≤o : ∀ {m n o} → m ⊔ n ≤ o → m ≤ o
    m⊔n≤o⇒m≤o m⊔n≤o = ≤-trans (m≤m⊔n _ _) m⊔n≤o

    m≤n⇒m≤o⊔n : ∀ {m n} o → m ≤ n → m ≤ o ⊔ n
    m≤n⇒m≤o⊔n o m≤n = ≤-trans m≤n (n≤m⊔n o _)
    
    m≤n⇒m≤n⊔o : ∀ {m n} o → m ≤ n → m ≤ n ⊔ o
    m≤n⇒m≤n⊔o o m≤n = ≤-trans m≤n (m≤m⊔n _ o)

    m≤n⇒o⊓m≤n : ∀ {m n} o → m ≤ n → o ⊓ m ≤ n
    m≤n⇒o⊓m≤n o m≤n = ≤-trans (m⊓n≤n o _) m≤n

    m≤n⇒m⊓o≤n : ∀ {m n} o → m ≤ n → m ⊓ o ≤ n
    m≤n⇒m⊓o≤n o m≤n = ≤-trans (m⊓n≤m _ o) m≤n
    
    
    -- stdlib
    m⊔n≤m+n : ∀ m n → m ⊔ n ≤ m + n
    m⊔n≤m+n m n with ⊔-sel m n
    ... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤m+n m n
    ... | inj₂ m⊔n≡n rewrite m⊔n≡n = n≤m+n m n

    -- stdlib
    m⊓n≤m+n : ∀ m n → m ⊓ n ≤ m + n
    m⊓n≤m+n m n with ⊓-sel m n
    ... | inj₁ m⊓n≡m rewrite m⊓n≡m = m≤m+n m n
    ... | inj₂ m⊓n≡n rewrite m⊓n≡n = n≤m+n m n

    


    ⊓-⊎preservesₗ-≤x : ∀ {x} → _⊓_ ⊎-Preservesₗ (_≤ x)
    ⊓-⊎preservesₗ-≤x n m≤x = ≤-trans (m⊓n≤m _ n) m≤x

    ⊓-⊎preservesᵣ-≤x : ∀ {x} → _⊓_ ⊎-Preservesᵣ (_≤ x)
    ⊓-⊎preservesᵣ-≤x m n≤x = ≤-trans (m⊓n≤n m _) n≤x

    ⊓-⊎preserves-≤x : ∀ {x} → _⊓_ ⊎-Preserves (_≤ x)
    ⊓-⊎preserves-≤x = ⊓-⊎preservesₗ-≤x , ⊓-⊎preservesᵣ-≤x

    ⊓-⊎preservesₗ-<x : ∀ {x} → _⊓_ ⊎-Preservesₗ (_< x)
    ⊓-⊎preservesₗ-<x n m<x = ≤-trans (s≤s (m⊓n≤m _ n)) m<x

    ⊓-⊎preservesᵣ-<x : ∀ {x} → _⊓_ ⊎-Preservesᵣ (_< x)
    ⊓-⊎preservesᵣ-<x m n<x = ≤-trans (s≤s (m⊓n≤n m _)) n<x

    ⊓-⊎preserves-<x : ∀ {x} → _⊓_ ⊎-Preserves (_< x)
    ⊓-⊎preserves-<x = ⊓-⊎preservesₗ-<x , ⊓-⊎preservesᵣ-<x
    
    ⊓-×preserves-x≤ : ∀ {x} → _⊓_ ×-Preserves (x ≤_)
    ⊓-×preserves-x≤ x≤a x≤b = subst (_≤ _) (⊓-idem _) (⊓-mono-≤ x≤a x≤b)
    

    ⊓-forces×-x≤ : ∀ {x} → _⊓_ Forces-× (x ≤_)
    ⊓-forces×-x≤ {_} {m} {n} x≤m⊓n = (≤-trans x≤m⊓n (m⊓n≤m m n) , ≤-trans x≤m⊓n (subst (_≤ n) (⊓-comm n m) (m⊓n≤m n m)))

    ⊔-⊎preservesₗ-x≤ : ∀ {x} → _⊔_ ⊎-Preservesₗ (x ≤_)
    ⊔-⊎preservesₗ-x≤ n x≤m = ≤-trans x≤m (m≤m⊔n _ n)
    
    ⊔-⊎preservesᵣ-x≤ : ∀ {x} → _⊔_ ⊎-Preservesᵣ (x ≤_)
    ⊔-⊎preservesᵣ-x≤ m x≤n = ≤-trans x≤n (n≤m⊔n m _)

    ⊔-⊎preserves-x≤ : ∀ {x} → _⊔_ ⊎-Preserves (x ≤_)
    ⊔-⊎preserves-x≤ = ⊔-⊎preservesₗ-x≤ , ⊔-⊎preservesᵣ-x≤

    ⊔-×preserves-≤x : ∀ {x} → _⊔_ ×-Preserves (_≤ x)
    ⊔-×preserves-≤x {x} {m} {n} m≤x n≤x with ⊔-sel m n
    ... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤x
    ... | inj₂ m⊔n≡n rewrite m⊔n≡n = n≤x

    ⊔-forces×-≤x : ∀ {x} → _⊔_ Forces-× (_≤ x)
    ⊔-forces×-≤x {_} {m} {n} m⊔n≤x = (≤-trans (m≤m⊔n m n) m⊔n≤x) , (≤-trans (subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)) m⊔n≤x)

    ⊔-preserves-≡x : ∀ {x} → _⊔_ ×-Preserves (_≡ x)
    ⊔-preserves-≡x refl refl = ⊔-idem _

    ⊔-preserves-x≡ : ∀ {x} → _⊔_ ×-Preserves (x ≡_)
    ⊔-preserves-x≡ refl refl = sym (⊔-idem _)

    ⊓-preserves-≡x : ∀ {x} → _⊓_ ×-Preserves (_≡ x)
    ⊓-preserves-≡x refl refl = ⊓-idem _

    ⊓-preserves-x≡ : ∀ {x} → _⊓_ ×-Preserves (x ≡_)
    ⊓-preserves-x≡ refl refl = sym (⊓-idem _)

    
    ⊓-triangulate : ∀ x y z → x ⊓ y ⊓ z ≡ (x ⊓ y) ⊓ (y ⊓ z)
    ⊓-triangulate x y z = begin
      x ⊓ y ⊓ z           ≡⟨ cong (λ v → x ⊓ v ⊓ z) (sym (⊓-idem y)) ⟩
      x ⊓ (y ⊓ y) ⊓ z     ≡⟨ ⊓-assoc x _ _ ⟩
      x ⊓ ((y ⊓ y) ⊓ z)   ≡⟨ cong (x ⊓_) (⊓-assoc y _ _) ⟩
      x ⊓ (y ⊓ (y ⊓ z))   ≡⟨ sym (⊓-assoc x _ _) ⟩
      (x ⊓ y) ⊓ (y ⊓ z)   ∎
      where open ≡-Reasoning


    -- + distributes over ⊔

    -- stdlib
    +-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
    +-distribˡ-⊔ zero    y z = refl
    +-distribˡ-⊔ (suc x) y z = cong suc (+-distribˡ-⊔ x y z)

    -- stdlib
    +-distribʳ-⊔ : _+_ DistributesOverʳ _⊔_
    +-distribʳ-⊔ x y z =
      begin
        (y ⊔ z) + x       ≡⟨ +-comm (y ⊔ z) x ⟩
        x + (y ⊔ z)       ≡⟨ +-distribˡ-⊔ x y z ⟩
        (x + y) ⊔ (x + z) ≡⟨ cong₂ _⊔_ (+-comm x y) (+-comm x z) ⟩
        (y + x) ⊔ (z + x)
      ∎
      where open ≡-Reasoning

    -- stdlib
    +-distrib-⊔ : _+_ DistributesOver _⊔_
    +-distrib-⊔ = +-distribˡ-⊔ , +-distribʳ-⊔


    -- + distributes over ⊓
    
    -- stdlib
    +-distribˡ-⊓ : _+_ DistributesOverˡ _⊓_
    +-distribˡ-⊓ zero    y z = refl
    +-distribˡ-⊓ (suc x) y z = cong suc (+-distribˡ-⊓ x y z)

    -- stdlib
    +-distribʳ-⊓ : _+_ DistributesOverʳ _⊓_
    +-distribʳ-⊓ x y z =
      begin
        (y ⊓ z) + x       ≡⟨ +-comm (y ⊓ z) x ⟩
        x + (y ⊓ z)       ≡⟨ +-distribˡ-⊓ x y z ⟩
        (x + y) ⊓ (x + z) ≡⟨ cong₂ _⊓_ (+-comm x y) (+-comm x z) ⟩
        (y + x) ⊓ (z + x)
      ∎
      where open ≡-Reasoning

    -- stdlib
    +-distrib-⊓ : _+_ DistributesOver _⊓_
    +-distrib-⊓ = +-distribˡ-⊓ , +-distribʳ-⊓
    
    -----------------
    -- Subtraction --
    -----------------

    -- stdlib
    +-∸-comm : ∀ {m} n {o} → o ≤ m → m + n ∸ o ≡ m ∸ o + n
    +-∸-comm {zero}  _ {suc o} ()
    +-∸-comm {zero}  _ {zero}  _         = refl
    +-∸-comm {suc m} _ {zero}  _         = refl
    +-∸-comm {suc m} n {suc o} (s≤s o≤m) = +-∸-comm n o≤m

    m∸n+n≡m : ∀ {m n} → n ≤ m → m ∸ n + n ≡ m
    m∸n+n≡m {m} {n} n≤m = trans (sym (+-∸-comm n n≤m)) (m+n∸n≡m m n)

    m∸[m∸n]≡n : ∀ {m n} → n ≤ m → m ∸ (m ∸ n) ≡ n
    m∸[m∸n]≡n {m}     {zero}  z≤n       = n∸n≡0 m
    m∸[m∸n]≡n {suc m} {suc n} (s≤s n≤m) = trans (+-∸-assoc 1 (n∸m≤n n m)) (cong suc (m∸[m∸n]≡n n≤m))
    
    ∸-monoᵣ-≤ : ∀ {m n o} → m ≤ n → o ≤ n → m ∸ o ≤ n ∸ o
    ∸-monoᵣ-≤ z≤n       (s≤s o≤n) = z≤n
    ∸-monoᵣ-≤ m≤n       z≤n       = m≤n
    ∸-monoᵣ-≤ (s≤s m≤n) (s≤s o≤n) = ∸-monoᵣ-≤ m≤n o≤n

    ∸-monoₗ-< : ∀ {m n o} → o < n → n < m → m ∸ n < m ∸ o
    ∸-monoₗ-< {_} {suc n} {zero}  (s≤s o<n) (s≤s n<m) = s≤s (n∸m≤n n _)
    ∸-monoₗ-< {_} {suc n} {suc o} (s≤s o<n) (s≤s n<m) = ∸-monoₗ-< o<n n<m
    
    m∸n≡0⇒m≤n : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
    m∸n≡0⇒m≤n {zero}  {_}    _   = z≤n
    m∸n≡0⇒m≤n {suc m} {zero} ()
    m∸n≡0⇒m≤n {suc m} {suc n} eq = s≤s (m∸n≡0⇒m≤n eq)

    m<n⇒0<n∸m : ∀ {m n} → m < n → 0 < n ∸ m
    m<n⇒0<n∸m {_}     {zero}  ()
    m<n⇒0<n∸m {zero}  {suc n} _         = s≤s z≤n
    m<n⇒0<n∸m {suc m} {suc n} (s≤s m<n) = m<n⇒0<n∸m m<n

    m<n⇒n∸m≡1+o : ∀ {m n} → m < n → ∃ λ o → n ∸ m ≡ suc o
    m<n⇒n∸m≡1+o {_}     {zero}  ()
    m<n⇒n∸m≡1+o {zero}  {suc n} (s≤s m<n) = n , refl
    m<n⇒n∸m≡1+o {suc m} {suc n} (s≤s m<n) = m<n⇒n∸m≡1+o m<n

    m≤n⇒o∸n≤o∸m : ∀ {m n} o → m ≤ n → o ∸ n ≤ o ∸ m
    m≤n⇒o∸n≤o∸m {_} {n} zero m≤n rewrite 0∸n≡0 n = z≤n
    m≤n⇒o∸n≤o∸m {_} {n} (suc o) z≤n = n∸m≤n n (suc o)
    m≤n⇒o∸n≤o∸m {_} {_} (suc o) (s≤s m≤n) = m≤n⇒o∸n≤o∸m o m≤n

    m<n≤o⇒o∸n<o∸m : ∀ {m n o} → m < n → n ≤ o → o ∸ n < o ∸ m
    m<n≤o⇒o∸n<o∸m {zero}  {suc n} (s≤s m<n) (s≤s n≤o) = s≤s (n∸m≤n n _)
    m<n≤o⇒o∸n<o∸m {suc m} {_}     (s≤s m<n) (s≤s n≤o) = m<n≤o⇒o∸n<o∸m m<n n≤o

    o∸n≤o∸m∧m≤o⇒m≤n : ∀ {m n o} → o ∸ n ≤ o ∸ m → m ≤ o → m ≤ n
    o∸n≤o∸m∧m≤o⇒m≤n {zero}  {_}     {_}     _ _ = z≤n
    o∸n≤o∸m∧m≤o⇒m≤n {suc m} {_}     {zero}  _ ()
    o∸n≤o∸m∧m≤o⇒m≤n {suc m} {zero}  {suc o} o+1≤o∸m n≤o = contradiction (≤-trans o+1≤o∸m (n∸m≤n m o)) 1+n≰n
    o∸n≤o∸m∧m≤o⇒m≤n {_}     {suc n} {_}     o∸n≤o∸m (s≤s m≤o) = s≤s (o∸n≤o∸m∧m≤o⇒m≤n o∸n≤o∸m m≤o)

    m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
    m≤n⇒m∸n≡0 {n = n} z≤n = 0∸n≡0 n
    m≤n⇒m∸n≡0 (s≤s m≤n)   = m≤n⇒m∸n≡0 m≤n

    m>n⇒m∸n≢0 : ∀ {m n} → m > n → m ∸ n ≢ 0
    m>n⇒m∸n≢0 {n = zero}  (s≤s m>n) = λ()
    m>n⇒m∸n≢0 {n = suc n} (s≤s m>n) = m>n⇒m∸n≢0 m>n


    -- _∸_ distributes over _⊓_ (sort of)
    
    ∸-distribˡ-⊓-⊔ : ∀ x y z → x ∸ (y ⊓ z) ≡ (x ∸ y) ⊔ (x ∸ z)
    ∸-distribˡ-⊓-⊔ x       zero    zero    = sym (⊔-idem x)
    ∸-distribˡ-⊓-⊔ zero    zero    (suc z) = refl
    ∸-distribˡ-⊓-⊔ zero    (suc y) zero    = refl
    ∸-distribˡ-⊓-⊔ zero    (suc y) (suc z) = refl
    ∸-distribˡ-⊓-⊔ (suc x) zero    (suc z) = sym (n≤m⇒m⊔n≡m (≤-step (n∸m≤n z x)))
    ∸-distribˡ-⊓-⊔ (suc x) (suc y) zero    = sym (trans (⊔-comm (x ∸ y) (suc x)) (n≤m⇒m⊔n≡m (≤-step (n∸m≤n y x))))
    ∸-distribˡ-⊓-⊔ (suc x) (suc y) (suc z) = ∸-distribˡ-⊓-⊔ x y z
    
    -- stdlib
    ∸-distribʳ-⊓ : _∸_ DistributesOverʳ _⊓_
    ∸-distribʳ-⊓ zero    y       z       = refl
    ∸-distribʳ-⊓ (suc x) zero    zero    = refl
    ∸-distribʳ-⊓ (suc x) zero    (suc z) = refl
    ∸-distribʳ-⊓ (suc x) (suc y) zero    = sym (0-zeᵣ-⊓ (y ∸ x))
    ∸-distribʳ-⊓ (suc x) (suc y) (suc z) = ∸-distribʳ-⊓ x y z

    -- _∸_ distributes over _⊔_ (sort of)
    
    ∸-distribˡ-⊔-⊓ : ∀ x y z → x ∸ (y ⊔ z) ≡ (x ∸ y) ⊓ (x ∸ z)
    ∸-distribˡ-⊔-⊓ x       zero    zero    = sym (⊓-idem x)
    ∸-distribˡ-⊔-⊓ zero    zero    (suc z) = refl
    ∸-distribˡ-⊔-⊓ zero    (suc y) zero    = refl
    ∸-distribˡ-⊔-⊓ zero    (suc y) (suc z) = refl
    ∸-distribˡ-⊔-⊓ (suc x) zero    (suc z) = sym (trans (⊓-comm (suc x) (x ∸ z)) (m≤n⇒m⊓n≡m (≤-step (n∸m≤n z x))))
    ∸-distribˡ-⊔-⊓ (suc x) (suc y) zero    = sym (m≤n⇒m⊓n≡m (≤-step (n∸m≤n y x)))
    ∸-distribˡ-⊔-⊓ (suc x) (suc y) (suc z) = ∸-distribˡ-⊔-⊓ x y z

    -- std-lib
    ∸-distribʳ-⊔ : _∸_ DistributesOverʳ _⊔_
    ∸-distribʳ-⊔ zero    y       z       = refl
    ∸-distribʳ-⊔ (suc x) zero    zero    = refl
    ∸-distribʳ-⊔ (suc x) zero    (suc z) = refl
    ∸-distribʳ-⊔ (suc x) (suc y) zero    = sym (0-idᵣ-⊔ (y ∸ x))
    ∸-distribʳ-⊔ (suc x) (suc y) (suc z) = ∸-distribʳ-⊔ x y z

    ∸-left-cancellative :  ∀ {x y z} → y ≤ x → z ≤ x → x ∸ y ≡ x ∸ z → y ≡ z
    ∸-left-cancellative {_} {_}     {_}     z≤n       z≤n       _       = refl
    ∸-left-cancellative {x} {_}     {suc z} z≤n       (s≤s z≤x) 1+x≡x∸z = contradiction (sym 1+x≡x∸z) (<⇒≢ (s≤s (n∸m≤n z _)))
    ∸-left-cancellative {x} {suc y} {_}     (s≤s y≤x) z≤n       x∸y≡1+x = contradiction x∸y≡1+x (<⇒≢ (s≤s (n∸m≤n y _)))
    ∸-left-cancellative {_} {_}     {_}     (s≤s y≤x) (s≤s z≤x) x∸y≡x∸z = cong suc (∸-left-cancellative y≤x z≤x x∸y≡x∸z)
    
    ≤-move-+ᵣ : ∀ {m} n {o} → m + n ≤ o → m ≤ o ∸ n
    ≤-move-+ᵣ {m} n {o} m+n≤o =
      begin
        m         ≡⟨ sym (m+n∸n≡m m n) ⟩
        m + n ∸ n ≤⟨ ∸-monoᵣ-≤ m+n≤o (m+n≤o⇒n≤o m m+n≤o) ⟩
        o ∸ n
      ∎
      where open ≤-Reasoning

    ≤-move-+ₗ : ∀ {m} n {o} → m ≤ n + o → m ∸ n ≤ o
    ≤-move-+ₗ {m} n {o} m≤n+o =
      begin
        m ∸ n     ≤⟨ ∸-monoᵣ-≤ m≤n+o (m≤m+n n o) ⟩
        n + o ∸ n ≡⟨ cong (_∸ n) (+-comm n _) ⟩
        o + n ∸ n ≡⟨ m+n∸n≡m o n ⟩
        o
      ∎
      where open ≤-Reasoning

    ≤-move-∸ᵣ : ∀ {m n o} → m ∸ n ≤ o → n ≤ m → m ≤ o + n
    ≤-move-∸ᵣ {m} {n} {o} m∸n≤o n≤m =
      begin
        m           ≡⟨ sym (m+n∸m≡n n≤m) ⟩
        n + (m ∸ n) ≡⟨ +-comm n _ ⟩
        m ∸ n + n   ≤⟨ m∸n≤o +-mono (≤-refl {n}) ⟩
        o + n
      ∎
      where open ≤-Reasoning

    m∸n≤o⇒m∸o≤n : ∀ {m n o} → n ≤ m → m ∸ n ≤ o → m ∸ o ≤ n
    m∸n≤o⇒m∸o≤n {o = o} n≤m m∸n≤o = ≤-move-+ₗ o (≤-move-∸ᵣ m∸n≤o n≤m)

    postulate m∸n<o⇒m∸o<n : ∀ {m n o} → n ≤ m → m ∸ n < o → m ∸ o < n
    --m∸n<o⇒m∸o<n {o = o} n≤m m∸n<o = {!!} --≤-move-+ₗ o (≤-move-∸ᵣ m∸n<o n<m)
    
    ≤-move-+-∸ᵣ : ∀ {m n} o {p} → m ∸ n + o ≤ p → n ≤ m → m ≤ p ∸ o + n
    ≤-move-+-∸ᵣ o m∸n+o≤p n≤m = ≤-move-∸ᵣ (≤-move-+ᵣ o m∸n+o≤p) n≤m

    ≡-move-∸ᵣ : ∀ {m n o} → m ∸ n ≡ o → n ≤ m → m ≡ o + n
    ≡-move-∸ᵣ {m} {n} {o} refl n≤m = trans (sym (m+n∸n≡m m n)) (+-∸-comm n n≤m)

    ≡-move-∸ₗ : ∀ {m n o} → m ≡ n ∸ o → o ≤ n → m + o ≡ n
    ≡-move-∸ₗ {m} {n} {o} refl o≤n = trans (+-comm m o) (m+n∸m≡n o≤n)

    ≡-move-+ᵣ : ∀ {m n o} → m + o ≡ n → m ≡ n ∸ o
    ≡-move-+ᵣ {m} {n} {o} refl = sym (m+n∸n≡m m o)

    ≡-move-+ₗ : ∀ {m n o} → m ≡ n + o → m ∸ o ≡ n
    ≡-move-+ₗ {m} {n} {o} refl = m+n∸n≡m n o
  
    ≡-move-+-∸ᵣ : ∀ {m n} o {p} → m ∸ n + o ≡ p → n ≤ m → m ≡ p ∸ o + n
    ≡-move-+-∸ᵣ o m∸n+o≤p n≤m = ≡-move-∸ᵣ (≡-move-+ᵣ m∸n+o≤p) n≤m

    w∸x≡y∸z⇒v+x≡w∧v+y≡z : ∀ {w x y z} → w ∸ x ≡ y ∸ z → x ≤ w → z ≤ y → ∃ λ v → (v + x ≡ w) × (v + z ≡ y)
    w∸x≡y∸z⇒v+x≡w∧v+y≡z {w} {x} {y} {z} x+o∸x≡y∸z x≤w z≤y with m≤n⇒m+o≡n x≤w
    ... | (o , refl) = o , +-comm o x , ≡-move-∸ₗ (
      begin
        o           ≡⟨ sym (m+n∸n≡m o x) ⟩
        o + x ∸ x   ≡⟨ cong (_∸ x) (+-comm o x) ⟩
        x + o ∸ x   ≡⟨ x+o∸x≡y∸z ⟩
        y ∸ z
      ∎) z≤y
      where open ≡-Reasoning

