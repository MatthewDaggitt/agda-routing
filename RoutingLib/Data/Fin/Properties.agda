
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective; _≟_; suc-injective; inject₁-lemma)
open import Data.Product using (_,_)
open import Data.Nat using (z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
open import Data.Nat.Properties using (1+n≰n)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_⇒_; _Respects₂_; _Respects_; Decidable; Reflexive; Irreflexive; Transitive; Total; Antisymmetric; IsDecTotalOrder; IsTotalOrder; IsPartialOrder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; isEquivalence; sym; trans)
open import Relation.Binary.Consequences using (trans∧tri⟶resp≈)
open import Function using (_on_; _∘_; flip)

open import RoutingLib.Data.Nat.Properties using (<⇒≢) renaming (≤-total to ≤ℕ-total; ≤-antisym to ≤ℕ-antisym; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import RoutingLib.Data.Fin

module RoutingLib.Data.Fin.Properties where

  ------------------------------------------------------------------------------
  -- Properties of _≤_

  -- stdlib
  ≤-reflexive : ∀ {n} → _≡_ ⇒ (_≤_ {n})
  ≤-reflexive refl = ≤ℕ-refl

  -- stdlib
  ≤-refl : ∀ {n} → Reflexive (_≤_ {n})
  ≤-refl {x = fzero} = z≤n
  ≤-refl {x = fsuc n} = s≤s ≤-refl

  -- stdlib
  ≤-trans : ∀ {n} → Transitive (_≤_ {n})
  ≤-trans = ≤ℕ-trans

  -- stdlib
  ≤-antisym : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
  ≤-antisym x≤y y≤x = toℕ-injective (≤ℕ-antisym x≤y y≤x)

  -- stdlib
  ≤-total : ∀ {n} → Total (_≤_ {n})
  ≤-total x y = ≤ℕ-total (toℕ x) (toℕ y)

  -- stdlib
  ≤-isPreorder : ∀{n} → IsPreorder _≡_ (_≤_ {n})
  ≤-isPreorder = record {
      isEquivalence = isEquivalence;
      reflexive = ≤-reflexive;
      trans = ≤-trans
    }

  -- stdlib
  ≤-isPartialOrder : ∀{n} → IsPartialOrder _≡_ (_≤_ {n})
  ≤-isPartialOrder = record {
      isPreorder = ≤-isPreorder;
      antisym = ≤-antisym
    }

  -- stdlib
  ≤-isTotalOrder : ∀ {n} → IsTotalOrder _≡_ (_≤_ {n})
  ≤-isTotalOrder = record {
      isPartialOrder = ≤-isPartialOrder ;
      total = ≤-total
    }

  ≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
  ≤-isDecTotalOrder = record {
      isTotalOrder = ≤-isTotalOrder ;
      _≟_ = _≟_ ;
      _≤?_ = _≤?_
    }
    
  ------------------------------------------------------------------------------
  -- Properties of _<_
  
  -- stdlib
  _<?_ : ∀ {n} → Decidable (_<_ {n = n})
  x <? y = suc (toℕ x) ≤ℕ? toℕ y

  <-irrefl : ∀ {n} → Irreflexive _≡_ (_<_ {n})
  <-irrefl refl x<x = 1+n≰n x<x
  
  ------------------------------------------------------------------------------
  -- Punchout

  -- stdlib
  punchdown-injective : ∀ {m} {i j k : Fin (suc m)} (i≢j : i ≢ j) (i≢k : i ≢ k) → punchdown i≢j ≡ punchdown i≢k → j ≡ k
  punchdown-injective {_}     {fzero}   {fzero}  {_}      i≢j _   _    = contradiction refl i≢j
  punchdown-injective {_}     {fzero}   {_}      {fzero}  _   i≢k _    = contradiction refl i≢k
  punchdown-injective {_}     {fzero}   {fsuc j} {fsuc k} _   _   pⱼ≡pₖ = cong fsuc pⱼ≡pₖ
  punchdown-injective {zero}  {fsuc ()}
  punchdown-injective {suc n} {fsuc i}  {fzero}  {fzero}  _   _    _   = refl
  punchdown-injective {suc n} {fsuc i}  {fzero}  {fsuc k} _   _   ()
  punchdown-injective {suc n} {fsuc i}  {fsuc j} {fzero}  _   _   ()
  punchdown-injective {suc n} {fsuc i}  {fsuc j} {fsuc k} i≢j i≢k pⱼ≡pₖ = cong fsuc (punchdown-injective (i≢j ∘ cong fsuc) (i≢k ∘ cong fsuc) (suc-injective pⱼ≡pₖ))

  -- stdlib
  punchup-injective : ∀ {m} k {i j : Fin m} → punchup k i ≡ punchup k j → i ≡ j
  punchup-injective fzero                      i+1≡j+1   = suc-injective i+1≡j+1
  punchup-injective (fsuc k) {fzero}  {fzero}  _         = refl
  punchup-injective (fsuc k) {fzero}  {fsuc j} ()
  punchup-injective (fsuc k) {fsuc i} {fzero}  ()
  punchup-injective (fsuc k) {fsuc i} {fsuc j} ↑i+1≡↑j+1 = cong fsuc (punchup-injective k (suc-injective ↑i+1≡↑j+1))

  -- stdlib
  punchupₖ≢k : ∀ {m} k {i : Fin m} → punchup k i ≢ k
  punchupₖ≢k fzero            ()
  punchupₖ≢k (fsuc k) {fzero} ()
  punchupₖ≢k (fsuc k) {fsuc i} = punchupₖ≢k k ∘ suc-injective

  -- stdlib
  punchdown-punchup : ∀ {m} {i j : Fin (suc m)} (i≢j : i ≢ j) → punchup i (punchdown i≢j) ≡ j
  punchdown-punchup {_} {fzero} {fzero} 0≢0 = contradiction refl 0≢0
  punchdown-punchup {_} {fzero} {fsuc j} _ = refl
  punchdown-punchup {zero} {fsuc ()}
  punchdown-punchup {suc m} {fsuc i} {fzero} i≢j  = refl
  punchdown-punchup {suc m} {fsuc i} {fsuc j} i≢j = cong fsuc (punchdown-punchup (i≢j ∘ cong fsuc))
  

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
{-
  m≰n⇨n<m : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → n < m
  m≰n⇨n<m m≰n = ≰⇨< m≰n
-}
  
  ≤fromℕ : ∀ k → (i : Fin (suc k)) → i ≤ fromℕ k
  ≤fromℕ _       fzero    = z≤n
  ≤fromℕ zero    (fsuc ())
  ≤fromℕ (suc k) (fsuc i) = s≤s (≤fromℕ k i)





