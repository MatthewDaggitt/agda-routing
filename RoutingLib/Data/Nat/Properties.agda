
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple using (+-comm; +-suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₁)
open import Relation.Binary using (Irreflexive; Trichotomous; Asymmetric; Decidable; tri<; tri≈; tri>; _Preserves₂_⟶_⟶_; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; module ≡-Reasoning)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)
open import Algebra
open import Algebra.FunctionProperties using (Idempotent; RightIdentity; Selective)

open import RoutingLib.Algebra.FunctionProperties using (_×-Preserves_; _⊎-Preserves_; _Forces-×_; _Forces-⊎_; ⊎Preserves⇨×Preserves; Forces×⇨Forces⊎; RightCancellative)


module RoutingLib.Data.Nat.Properties where

  open import Data.Nat.Properties.Simple public
  open ≡-Reasoning

  abstract

    ----------------------
    -- Pushed to stdlib --
    ----------------------

    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

    open DistributiveLattice Data.Nat.Properties.distributiveLattice using () renaming (∨-comm to ⊓-comm; ∧-comm to ⊔-comm) public

    0-idᵣ-⊔ : RightIdentity _≡_ zero _⊔_
    0-idᵣ-⊔ zero = refl
    0-idᵣ-⊔ (suc x) = refl

    open Relation.Binary.DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans; total to ≤-total; antisym to ≤-antisym) public

    cmp : Trichotomous _≡_ _<_
    cmp zero    zero    = tri≈ (λ())     refl  (λ())
    cmp zero    (suc n) = tri< (s≤s z≤n) (λ()) (λ())
    cmp (suc m) zero    = tri> (λ())     (λ()) (s≤s z≤n)
    cmp (suc m) (suc n) with cmp m n
    ... | tri< m≤n m≢n n≰m = tri< (s≤s m≤n)      (m≢n ∘ suc-injective) (n≰m ∘ ≤-pred)
    ... | tri≈ m≰n m≡n n≰m = tri≈ (m≰n ∘ ≤-pred) (cong suc m≡n)        (n≰m ∘ ≤-pred)
    ... | tri> m≰n m≢n n≤m = tri> (m≰n ∘ ≤-pred) (m≢n ∘ suc-injective) (s≤s n≤m)

    ⊓-idem : Idempotent _≡_ _⊓_
    ⊓-idem x with ⊓-sel x x
    ... | inj₁ x⊓x≈x = x⊓x≈x
    ... | inj₂ x⊓x≈x = x⊓x≈x

    ⊔-idem : Idempotent _≡_ _⊔_
    ⊔-idem x with ⊔-sel x x
    ... | inj₁ x⊔x≈x = x⊔x≈x
    ... | inj₂ x⊔x≈x = x⊔x≈x

    <-irrefl : Irreflexive _≡_ _<_
    <-irrefl refl (s≤s n<n) = <-irrefl refl n<n

    <-asym : Asymmetric _<_
    <-asym (s≤s n<m) (s≤s m<n) = <-asym n<m m<n

    -----------------------
    -- To push to stdlib --
    -----------------------

    _<?_ : Decidable _<_
    x <? y = suc x ≤? y

    m⊓n≤n : ∀ m n → m ⊓ n ≤ n
    m⊓n≤n m n = subst (_≤ n) (⊓-comm n m) (m⊓n≤m n m)

    n≤m⊔n : ∀ m n → n ≤ m ⊔ n
    n≤m⊔n m n = subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)

    ⊔-pres-≤ : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
    ⊔-pres-≤ {x} {y} {u} {v} x≤y u≤v with ⊔-sel x u
    ... | inj₁ x⊔u≡x rewrite x⊔u≡x = ≤-trans x≤y (m≤m⊔n y v)
    ... | inj₂ x⊔u≡u rewrite x⊔u≡u = ≤-trans u≤v (n≤m⊔n y v)
  {-
    ⊓-pres-≥ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
    ⊓-pres-≥ {x} {y} {u} {v} x≥y u≥v with ⊓-sel x u
    ... | inj₁ x⊓u≡x rewrite x⊓u≡x = {!≤-trans x≤y (m≤m⊔n y v)!}
    ... | inj₂ x⊓u≡u rewrite x⊓u≡u = {!!}
  -}
  

    cancel-+-right : RightCancellative _≡_ _+_
    cancel-+-right {m} {n} o m+o≡n+o = cancel-+-left o (trans (+-comm o m) (trans m+o≡n+o (+-comm n o)))

    m≤n⇨m+o≡n : ∀ {m n} → m ≤ n → ∃ λ o → m + o ≡ n
    m≤n⇨m+o≡n {_} {n} z≤n = n , refl
    m≤n⇨m+o≡n (s≤s m≤n) with m≤n⇨m+o≡n m≤n
    ... | o , m+o≡n = o , cong suc m+o≡n

    ≤-stepsᵣ : ∀ {m n} k → m ≤ n → m ≤ n + k
    ≤-stepsᵣ {m} {n} k m≤n = subst (m ≤_) (+-comm k n) (≤-steps k m≤n)

    -----------
    -- Other --
    -----------
  
    -- Orders

    <⇒≤ : _<_ ⇒ _≤_
    <⇒≤ (s≤s m≤n) = ≤-trans m≤n (≤-step ≤-refl)
  
    <⇒≢ : _<_ ⇒ _≢_
    <⇒≢ m<n refl = 1+n≰n m<n

    <⇒≱ : _<_ ⇒ _≱_
    <⇒≱ (s≤s m+1≤n) (s≤s n≤m) = <⇒≱ m+1≤n n≤m

    <⇒≯ : _<_ ⇒ _≯_
    <⇒≯ (s≤s p<q) (s≤s q<p) = <⇒≯ p<q q<p

    ≮⇒≥ : _≮_ ⇒ _≥_
    ≮⇒≥ {_}     {zero}  _       = z≤n
    ≮⇒≥ {zero}  {suc j} 1≮j+1   = contradiction (s≤s z≤n) 1≮j+1
    ≮⇒≥ {suc i} {suc j} i+1≮j+1 = s≤s (≮⇒≥ (i+1≮j+1 ∘ s≤s))

    ≰⇒≥ : _≰_ ⇒ _≥_
    ≰⇒≥ {_}     {zero}  _       = z≤n
    ≰⇒≥ {zero}  {suc j} 0≰j+1   = contradiction z≤n 0≰j+1
    ≰⇒≥ {suc i} {suc j} i+1≰j+1 = s≤s (≰⇒≥ (i+1≰j+1 ∘ s≤s))

    ≤+≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
    ≤+≢⇒< {zero} {zero} m≤n m≢n = contradiction refl m≢n
    ≤+≢⇒< {zero} {suc n} m≤n m≢n = s≤s z≤n
    ≤+≢⇒< {suc m} {zero} ()
    ≤+≢⇒< {suc m} {suc n} (s≤s m≤n) s[m]≢s[n] = s≤s (≤+≢⇒< m≤n (λ m≡n → s[m]≢s[n] (cong suc m≡n)))


  
    -- Arithmetic

    n≤m⇨s[m]∸n≡s[n∸m] : ∀ {m n} → n ≤ m → suc m ∸ n ≡ suc (m ∸ n)
    n≤m⇨s[m]∸n≡s[n∸m] z≤n = refl
    n≤m⇨s[m]∸n≡s[n∸m] (s≤s n≤m) = n≤m⇨s[m]∸n≡s[n∸m] n≤m

    ∀x≤m:n≢x⇒m<n : ∀ m n → (∀ {x} → x ≤ m → n ≢ x) → m < n
    ∀x≤m:n≢x⇒m<n _ zero    x≤m⇒n≢x = contradiction refl (x≤m⇒n≢x z≤n)
    ∀x≤m:n≢x⇒m<n zero (suc n) x≤0⇒n≢x = s≤s z≤n
    ∀x≤m:n≢x⇒m<n (suc m) (suc n) x≤m+1⇒n≢x = s≤s (∀x≤m:n≢x⇒m<n m n (λ x≤m n≡x → x≤m+1⇒n≢x (s≤s x≤m) (cong suc n≡x)))

    m∸n≡0⇒m≤n : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
    m∸n≡0⇒m≤n {zero}  {_}    _   = z≤n
    m∸n≡0⇒m≤n {suc m} {zero} ()
    m∸n≡0⇒m≤n {suc m} {suc n} eq = s≤s (m∸n≡0⇒m≤n eq)

    m<n⇨0<n∸m : ∀ {m n} → m < n → 0 < n ∸ m
    m<n⇨0<n∸m {_}     {zero}  ()
    m<n⇨0<n∸m {zero}  {suc n} _         = s≤s z≤n
    m<n⇨0<n∸m {suc m} {suc n} (s≤s m<n) = m<n⇨0<n∸m m<n

    m<n⇒n∸m≡1+o : ∀ {m n} → m < n → ∃ λ o → n ∸ m ≡ suc o
    m<n⇒n∸m≡1+o {_}     {zero}  ()
    m<n⇒n∸m≡1+o {zero}  {suc n} (s≤s m<n) = n , refl
    m<n⇒n∸m≡1+o {suc m} {suc n} (s≤s m<n) = m<n⇒n∸m≡1+o m<n

    m<n⇨n≡o+1 : ∀ {m n} → m < n → ∃ λ o → n ≡ suc o
    m<n⇨n≡o+1 {_} {zero} ()
    m<n⇨n≡o+1 {_} {suc o} m<n = o , refl

    m+n≮n : ∀ m n → m + n ≮ n
    m+n≮n _ zero ()
    m+n≮n zero (suc n) (s≤s n<n) = m+n≮n zero n n<n
    m+n≮n (suc m) (suc n) (s≤s m+n≮) = m+n≮n m (suc n) (≤-trans m+n≮ (≤-step ≤-refl))
  
    m+1+n≢n : ∀ m n → suc m + n ≢ n
    m+1+n≢n zero _ ()
    m+1+n≢n (suc m) zero ()
    m+1+n≢n (suc m) (suc n) x = m+1+n≢n (suc m) n (trans (cong suc (sym (+-suc m n))) (suc-injective x))

    m<n⇨m+o+1≡n : ∀ {m n} → m < n → ∃ λ o → suc m + o ≡ n
    m<n⇨m+o+1≡n {_} {suc n} (s≤s z≤n) = n , refl
    m<n⇨m+o+1≡n (s≤s (s≤s m<n)) with m<n⇨m+o+1≡n (s≤s m<n)
    ... | o , m+o+1≡n = o , (cong suc m+o+1≡n)

    m≤n⇨o∸n≤o∸m : ∀ {m n} o → m ≤ n → o ∸ n ≤ o ∸ m
    m≤n⇨o∸n≤o∸m {_} {n} zero m≤n rewrite 0∸n≡0 n = z≤n
    m≤n⇨o∸n≤o∸m {_} {n} (suc o) z≤n = n∸m≤n n (suc o)
    m≤n⇨o∸n≤o∸m {_} {_} (suc o) (s≤s m≤n) = m≤n⇨o∸n≤o∸m o m≤n

    m<n≤o⇨o∸n<o∸m : ∀ {m n o} → m < n → n ≤ o → o ∸ n < o ∸ m
    m<n≤o⇨o∸n<o∸m {zero}  {suc n} (s≤s m<n) (s≤s n≤o) = s≤s (n∸m≤n n _)
    m<n≤o⇨o∸n<o∸m {suc m} {_}     (s≤s m<n) (s≤s n≤o) = m<n≤o⇨o∸n<o∸m m<n n≤o
  
    o∸n≤o∸m∧m≤o⇨m≤n : ∀ {m n o} → o ∸ n ≤ o ∸ m → m ≤ o → m ≤ n
    o∸n≤o∸m∧m≤o⇨m≤n {zero}  {_}     {_}     _ _ = z≤n
    o∸n≤o∸m∧m≤o⇨m≤n {suc m} {_}     {zero}  _ ()
    o∸n≤o∸m∧m≤o⇨m≤n {suc m} {zero}  {suc o} o+1≤o∸m n≤o = contradiction (≤-trans o+1≤o∸m (n∸m≤n m o)) 1+n≰n
    o∸n≤o∸m∧m≤o⇨m≤n {_}     {suc n} {_}     o∸n≤o∸m (s≤s m≤o) = s≤s (o∸n≤o∸m∧m≤o⇨m≤n o∸n≤o∸m m≤o)

    m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
    m≤n⇒m∸n≡0 {n = n} z≤n = 0∸n≡0 n
    m≤n⇒m∸n≡0 (s≤s m≤n)   = m≤n⇒m∸n≡0 m≤n

    m>n⇒m∸n≢0 : ∀ {m n} → m > n → m ∸ n ≢ 0
    m>n⇒m∸n≢0 {n = zero}  (s≤s m>n) = λ()
    m>n⇒m∸n≢0 {n = suc n} (s≤s m>n) = m>n⇒m∸n≢0 m>n

    -- ⊓ & ⊔

    m≰n⇨m⊓n≡m : ∀ {m n} → m ≰ n → m ⊓ n ≡ n
    m≰n⇨m⊓n≡m {zero}  {_}     m≰n = contradiction z≤n m≰n
    m≰n⇨m⊓n≡m {suc m} {zero}  m≰n = refl
    m≰n⇨m⊓n≡m {suc m} {suc n} m≰n = cong suc (m≰n⇨m⊓n≡m (λ m≤n → m≰n (s≤s m≤n)))
  
    m≤n⇨m⊓n≡m : ∀ {m n} → m ≤ n → m ⊓ n ≡ m
    m≤n⇨m⊓n≡m z≤n       = refl
    m≤n⇨m⊓n≡m (s≤s m≤n) = cong suc (m≤n⇨m⊓n≡m m≤n)

    m⊔n≤m+n : ∀ m n → m ⊔ n ≤ m + n
    m⊔n≤m+n m n with ⊔-sel m n
    ... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤m+n m n
    ... | inj₂ m⊔n≡n rewrite m⊔n≡n = n≤m+n m n

    m⊓n≤m+n : ∀ m n → m ⊓ n ≤ m + n
    m⊓n≤m+n m n with ⊓-sel m n
    ... | inj₁ m⊓n≡m rewrite m⊓n≡m = m≤m+n m n
    ... | inj₂ m⊓n≡n rewrite m⊓n≡n = n≤m+n m n

    m⊔n≡m⇨n≤m : ∀ {m n} → m ⊔ n ≡ m → n ≤ m
    m⊔n≡m⇨n≤m {m} {n} m⊔n≡m rewrite sym m⊔n≡m = n≤m⊔n m n

    n⊔m≡m⇨n≤m : ∀ {m n} → n ⊔ m ≡ m → n ≤ m
    n⊔m≡m⇨n≤m {m} {n} m⊔n≡m = m⊔n≡m⇨n≤m (trans (⊔-comm m n) m⊔n≡m)

    n≢0⇒0<n : ∀ {n} → n ≢ 0 → 0 < n
    n≢0⇒0<n {zero} 0≢0 = contradiction refl 0≢0
    n≢0⇒0<n {suc n} n+1≢0 = s≤s z≤n
  
    n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
    n≤0⇒n≡0 z≤n = refl


    ⊓-⊎preserves-≤x : ∀ {x} → _⊓_ ⊎-Preserves (_≤ x)
    ⊓-⊎preserves-≤x {_} {m} {n} (inj₁ m≤x) = ≤-trans (m⊓n≤m m n) m≤x
    ⊓-⊎preserves-≤x {_} {m} {n} (inj₂ n≤x) = ≤-trans (m⊓n≤n m n) n≤x

    ⊓-×preserves-≤x : ∀ {x} → _⊓_ ×-Preserves (_≤ x)
    ⊓-×preserves-≤x {x} = ⊎Preserves⇨×Preserves _⊓_ (_≤ x) ⊓-⊎preserves-≤x

    ⊓-forces×-x≤ : ∀ {x} → _⊓_ Forces-× (x ≤_)
    ⊓-forces×-x≤ {_} {m} {n} x≤m⊓n = (≤-trans x≤m⊓n (m⊓n≤m m n) , ≤-trans x≤m⊓n (subst (_≤ n) (⊓-comm n m) (m⊓n≤m n m)))

    ⊓-forces⊎-x≤ : ∀ {x} → _⊓_ Forces-⊎ (x ≤_)
    ⊓-forces⊎-x≤ {x} = Forces×⇨Forces⊎ _⊓_ (x ≤_) ⊓-forces×-x≤



    ⊔-⊎preserves-x≤ : ∀ {x} → _⊔_ ⊎-Preserves (x ≤_)
    ⊔-⊎preserves-x≤ {_} {_} {_} (inj₁ x≤m) = ≤-trans x≤m (m≤m⊔n _ _)
    ⊔-⊎preserves-x≤ {_} {m} {n} (inj₂ x≤n) = ≤-trans x≤n (n≤m⊔n m n)

    ⊔-×preserves-x≤ : ∀ {x} → _⊔_ ×-Preserves (x ≤_)
    ⊔-×preserves-x≤ x≤m _ = ⊔-⊎preserves-x≤ (inj₁ x≤m)

    ⊔-×preserves-≤x : ∀ {x} → _⊔_ ×-Preserves (_≤ x)
    ⊔-×preserves-≤x {x} {m} {n} m≤x n≤x with ⊔-sel m n
    ... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤x
    ... | inj₂ m⊔n≡n rewrite m⊔n≡n = n≤x

    ⊔-forces×-≤x : ∀ {x} → _⊔_ Forces-× (_≤ x)
    ⊔-forces×-≤x {_} {m} {n} m⊔n≤x = (≤-trans (m≤m⊔n m n) m⊔n≤x) , (≤-trans (subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)) m⊔n≤x)

    ⊔-forces⊎-≤x : ∀ {x} → _⊔_ Forces-⊎ (_≤ x)
    ⊔-forces⊎-≤x {x} = Forces×⇨Forces⊎ _⊔_ (_≤ x) ⊔-forces×-≤x


    ⊔-preserves-≡x : ∀ {x} → _⊔_ ×-Preserves (_≡ x)
    ⊔-preserves-≡x refl refl = ⊔-idem _

    ⊔-preserves-x≡ : ∀ {x} → _⊔_ ×-Preserves (x ≡_)
    ⊔-preserves-x≡ refl refl = sym (⊔-idem _)

    ⊓-preserves-≡x : ∀ {x} → _⊓_ ×-Preserves (_≡ x)
    ⊓-preserves-≡x refl refl = ⊓-idem _

    ⊓-preserves-x≡ : ∀ {x} → _⊓_ ×-Preserves (x ≡_)
    ⊓-preserves-x≡ refl refl = sym (⊓-idem _)

    m≡n∸o⇒m+o≡n : ∀ {m n o} → m ≡ n ∸ o → o ≤ n → m + o ≡ n
    m≡n∸o⇒m+o≡n {m} {n} {o} refl o≤n =
      begin
        (n ∸ o) + o ≡⟨ +-comm (n ∸ o) o ⟩ 
        o + (n ∸ o) ≡⟨ sym (+-∸-assoc o o≤n) ⟩
        o + n ∸ o   ≡⟨ cong (_∸ o) (+-comm o n) ⟩ 
        n + o ∸ o   ≡⟨ +-∸-assoc n (≤-refl {o}) ⟩ 
        n + (o ∸ o) ≡⟨ cong (n +_) (n∸n≡0 o) ⟩ 
        n + 0       ≡⟨ +-right-identity n ⟩ 
        n
      ∎
  
    w∸x≡y∸z⇒v+x≡w∧v+y≡z : ∀ {w x y z} → w ∸ x ≡ y ∸ z → x ≤ w → z ≤ y → ∃ λ v → (v + x ≡ w) × (v + z ≡ y)
    w∸x≡y∸z⇒v+x≡w∧v+y≡z {w} {x} {y} {z} x+o∸x≡y∸z x≤w z≤y with m≤n⇨m+o≡n x≤w
    ... | (o , refl) = o , +-comm o x , m≡n∸o⇒m+o≡n (
      begin
        o           ≡⟨ sym (+-right-identity o) ⟩
        o + 0       ≡⟨ cong (o +_) (sym (n∸n≡0 x)) ⟩
        o + (x ∸ x) ≡⟨ sym (+-∸-assoc o (≤-refl {x})) ⟩
        o + x ∸ x   ≡⟨ cong (_∸ x) (+-comm o x) ⟩
        x + o ∸ x   ≡⟨ x+o∸x≡y∸z ⟩
        y ∸ z
      ∎) z≤y


  +-∸-comm : ∀ {m} n {o} → o ≤ m → m + n ∸ o ≡ m ∸ o + n
  +-∸-comm {zero}  _ {suc o} ()
  +-∸-comm {zero}  _ {zero}  _         = refl
  +-∸-comm {suc m} _ {zero}  _         = refl
  +-∸-comm {suc m} n {suc o} (s≤s o≤m) = +-∸-comm n o≤m
{-
  +-∸-comm2 : ∀ m n o →  m + (n ∸ o) ≡ (m ∸ o) + n
  +-∸-comm2 zero zero zero = refl
  +-∸-comm2 zero zero (suc o) = refl
  +-∸-comm2 zero (suc n) zero = refl
  +-∸-comm2 zero (suc n) (suc o) = {!!}
  +-∸-comm2 (suc m) zero zero = refl
  +-∸-comm2 (suc m) zero (suc o) = {!!}
  +-∸-comm2 (suc m) (suc n) zero = refl
  +-∸-comm2 (suc m) (suc n) (suc o) = {!!}
-}
