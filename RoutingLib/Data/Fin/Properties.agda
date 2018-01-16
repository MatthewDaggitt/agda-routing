open import Algebra.FunctionProperties
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties
open import Data.Product using (_,_)
open import Data.Nat using (z≤n; s≤s; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
open import Data.Nat.Properties using (1+n≰n; <⇒≢)  renaming (≤-total to ≤ℕ-total; ≤-antisym to ≤ℕ-antisym; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_⇒_; _Respects₂_; _Respects_; Decidable; Reflexive; Irreflexive; Transitive; Total; Antisymmetric; IsDecTotalOrder; IsTotalOrder; IsPartialOrder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans)
open import Relation.Binary.Consequences using (trans∧tri⟶resp≈)
open import Function using (_on_; _∘_; flip)

open import RoutingLib.Data.Fin
open import RoutingLib.Data.Nat.Properties using (≤-cardinality)

module RoutingLib.Data.Fin.Properties where

  ------------------------------------------------------------------------------
  -- Properties of _≤_

  ≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
  ≤-isDecTotalOrder = record {
      isTotalOrder = ≤-isTotalOrder ;
      _≟_ = _≟_ ;
      _≤?_ = _≤?_
    }
    
  ------------------------------------------------------------------------------
  -- Properties of _<_
  
  <-irrefl : ∀ {n} → Irreflexive _≡_ (_<_ {n})
  <-irrefl refl x<x = 1+n≰n x<x
  
  ------------------------------------------------------------------------------
  -- Punchout

  -----------------------
  -- To push to stdlib --
  -----------------------

  inject₁-injective : ∀ {n} {i j : Fin n} → inject₁ i ≡ inject₁ j → i ≡ j
  inject₁-injective {i = fzero}  {fzero}  i≡j = refl
  inject₁-injective {i = fzero}  {fsuc j} ()
  inject₁-injective {i = fsuc i} {fzero}  ()
  inject₁-injective {i = fsuc i} {fsuc j} i≡j = cong fsuc (inject₁-injective (suc-injective i≡j))


  -------------------------
  -- Ordering properties --
  -------------------------

  <⇒≤pred : ∀ {n} {i j : Fin n} → j < i → j ≤ pred i
  <⇒≤pred {_} {fzero} {_} ()
  <⇒≤pred {_} {fsuc i} {fzero} j<i = z≤n
  <⇒≤pred {_} {fsuc i} {fsuc j} (s≤s j<i) = subst (_ ≤ℕ_) (sym (inject₁-lemma i)) j<i

  ≤-respₗ-≡ : ∀ {n x} → ((_≤_ {n}) x) Respects _≡_
  ≤-respₗ-≡ refl x≤y = x≤y

  ≤-respᵣ-≡ : ∀ {n x} → (flip (_≤_ {n}) x) Respects _≡_
  ≤-respᵣ-≡ refl x≤y = x≤y

  ≤-resp₂-≡ : ∀ {n} → (_≤_ {n}) Respects₂ _≡_
  ≤-resp₂-≡ = ≤-respₗ-≡ , ≤-respᵣ-≡

  

  ≤+≢⇒< : ∀ {n} {i j : Fin n} → i ≤ j → i ≢ j → i < j
  ≤+≢⇒< {i = fzero}  {fzero}  _         0≢0     = contradiction refl 0≢0
  ≤+≢⇒< {i = fzero}  {fsuc j} _         _       = s≤s z≤n
  ≤+≢⇒< {i = fsuc i} {fzero}  ()
  ≤+≢⇒< {i = fsuc i} {fsuc j} (s≤s i≤j) 1+i≢1+j = s≤s (≤+≢⇒< i≤j (1+i≢1+j ∘ (cong fsuc)))

  -----------
  -- Other --
  -----------

  suc≢zero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
  suc≢zero ()

  m<n⇨m≢n : ∀ {n₁} {m n : Fin n₁} → m < n → m ≢ n
  m<n⇨m≢n m<n m≡n = (<⇒≢ m<n) (cong toℕ m≡n)

  m≰n⇨m≢n : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → m ≢ n
  m≰n⇨m≢n m≰n refl = m≰n ≤ℕ-refl
  
  ≤fromℕ : ∀ k → (i : Fin (suc k)) → i ≤ fromℕ k
  ≤fromℕ _       fzero    = z≤n
  ≤fromℕ zero    (fsuc ())
  ≤fromℕ (suc k) (fsuc i) = s≤s (≤fromℕ k i)

  fromℕ≤-cong : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) → i ≡ j → fromℕ≤ i<n ≡ fromℕ≤ j<n
  fromℕ≤-cong i<n j<n refl = cong fromℕ≤ (≤-cardinality i<n j<n)

  fromℕ≤-mono-≤ : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                   i ≤ℕ j → fromℕ≤ i<n ≤ fromℕ≤ j<n
  fromℕ≤-mono-≤ (s≤s z≤n)       (s≤s _)         z≤n       = z≤n
  fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s z≤n)       ()
  fromℕ≤-mono-≤ (s≤s (s≤s i<n)) (s≤s (s≤s j<n)) (s≤s i≤j) =
    s≤s (fromℕ≤-mono-≤ (s≤s i<n) (s≤s j<n) i≤j)

  postulate fromℕ≤-mono⁻¹-< : ∀ {n i j} (i<n : i <ℕ n) (j<n : j <ℕ n) →
                              fromℕ≤ i<n < fromℕ≤ j<n → i <ℕ j 
  --------------------
  -- Absorbing _+↑_ --
  --------------------

  
  postulate +↑-comm : ∀ {n} → Commutative {A = Fin n} _≡_ _+↑_

  postulate i∔j≡n : ∀ {n} {i j : Fin (suc n)} → n ≤ℕ toℕ (i + j) → i +↑ j ≡ fromℕ n
