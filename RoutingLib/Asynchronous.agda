open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_; all?)
open import Data.Nat using (ℕ; _<_; s≤s; zero; suc)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Bool using (Bool)
open import Data.Product using (∃; _×_; proj₂; _,_)
open import Relation.Binary using (_⇒_; Reflexive; Symmetric; Transitive; IsEquivalence; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬∀⟶∃¬; contradiction)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Data.Nat.Properties using (≤-refl)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Asynchronous.Schedule using (Schedule; syncSchedule)

module RoutingLib.Asynchronous where

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed as σᵢ and carried out on n separate processors 
  record Parallelisation a ℓ (n : ℕ) : Set (lsuc (a ⊔ ℓ)) where
    field
      -- The type of information at each processor
      Sᵢ : Fin n → DecSetoid a ℓ
      -- The update function for each processor
      σᵢ : ∀ i → (∀ j → DecSetoid.Carrier (Sᵢ j)) → DecSetoid.Carrier (Sᵢ i)
      -- All update functions are congruent
      σᵢ-cong : ∀ {i} {X} {Y} → (∀ j → DecSetoid._≈_ (Sᵢ j) (X j) (Y j)) → DecSetoid._≈_ (Sᵢ i) (σᵢ i X) (σᵢ i Y)

    module _ {i} where
      open DecSetoid (Sᵢ i)
        renaming (
          Carrier to Mᵢ;
          _≈_ to _≈ᵢ_;
          _≟_ to _≟ᵢ_;
          refl to ≈ᵢ-refl;
          sym to ≈ᵢ-sym;
          trans to ≈ᵢ-trans
        ) public

    -- The overall state space
    M : Set a
    M = (∀ i → Mᵢ {i})
    
    σ : M → M
    σ X i = σᵢ i X

    -- Equality over M
    _≈ₘ_ : Rel M ℓ
    X ≈ₘ Y = ∀ i → X i ≈ᵢ Y i

    _≉ₘ_ : Rel M ℓ
    X ≉ₘ Y = ¬ (X ≈ₘ Y)

    ≈ₘ-reflexive : _≡_ ⇒ _≈ₘ_
    ≈ₘ-reflexive refl i = ≈ᵢ-refl

    ≈ₘ-refl : Reflexive _≈ₘ_
    ≈ₘ-refl i = ≈ᵢ-refl

    ≈ₘ-sym : Symmetric _≈ₘ_
    ≈ₘ-sym A≈B i = ≈ᵢ-sym (A≈B i)

    ≈ₘ-trans : Transitive _≈ₘ_
    ≈ₘ-trans A≈B B≈C i = ≈ᵢ-trans (A≈B i) (B≈C i)

    _≟ₘ_ : Decidable _≈ₘ_
    X ≟ₘ Y = all? (λ i → X i ≟ᵢ Y i)

    ≉ₘ-witness : ∀ {X Y} → X ≉ₘ Y → ∃ λ i → ¬ (X i ≈ᵢ Y i)
    ≉ₘ-witness {X} {Y} X≉Y with all? (λ i → X i ≟ᵢ Y i)
    ... | yes all  = contradiction all X≉Y
    ... | no  ¬all = ¬∀⟶∃¬ n (λ i → X i ≈ᵢ Y i) (λ i → X i ≟ᵢ Y i) ¬all

    ≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
    ≈ₘ-isEquivalence = record { 
      refl = ≈ₘ-refl ; 
      sym = ≈ₘ-sym ; 
      trans = ≈ₘ-trans }

    Sₘ : Setoid a ℓ
    Sₘ = record {
      Carrier = M;
      _≈_ = _≈ₘ_ ;
      isEquivalence = ≈ₘ-isEquivalence}





  --------------------------------------------
  -- Properties of parallelisable functions --
  --------------------------------------------

  module _ {a ℓ n} (f : Parallelisation a ℓ n) where

    open Parallelisation f
    
    δ^' : Schedule n → ∀ {t} → Acc _<_ t → M → M
    δ^' sch {zero}  _           X = X
    δ^' sch {suc t} (acc tAcc) X i with i ∈? (Schedule.α sch) (suc t)
    ... | no  i∉αₜ = δ^' sch (tAcc t ≤-refl) X i
    ... | yes i∈αₜ = σᵢ i (λ k → δ^' sch (tAcc (β (suc t) i k) (causality t i k)) X k)
      where open Schedule sch

    -- The asynchronous state function
    δ^ : Schedule n → ℕ → M → M
    δ^ sch t = δ^' sch (<-wf t)








    -- The synchronous state function
    σ^ : ℕ → M → M
    σ^ = δ^ (syncSchedule n)

    -- A record encapsulating the idea that f is a well behaved parallelisable function
    record IsAsynchronouslySafe : Set (lsuc (a ⊔ ℓ)) where
      field
        m*         : M
        m*-fixed   : σ m* ≈ₘ m*
        m*-unique  : ∀ {x} → σ x ≈ₘ x → x ≈ₘ m*
        m*-reached : ∀ sch X → ∃ λ tᶜ → ∀ {t} → tᶜ < t → δ^ sch t X ≈ₘ m*
