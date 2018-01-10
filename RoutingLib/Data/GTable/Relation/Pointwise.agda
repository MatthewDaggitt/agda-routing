open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (all?)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary using (REL; Setoid)
open import Relation.Binary.Indexed using () renaming (Rel to IRel)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Data.GTable

module RoutingLib.Data.GTable.Relation.Pointwise where

  Pointwise : ∀ {a b ℓ n} {A : Table (Set a) n} {B : Table (Set b) n} →
              GTable n (λ i → REL (A i) (B i) ℓ) →
              REL (GTable n A) (GTable n B) ℓ
  Pointwise _≈_ A B = ∀ i → _≈_ i (A i) (B i)

  -- i₁i₂=ℓ₀
  -- I₁I₂=Fin n

{-

  --∀ {a₁ a₂} → (Fin n → Set a₁) → (Fin n → Set a₂) → (ℓ : Level) → Set _
      
  PW : ∀ {a b ℓ n} {A : Table (Set a) n} {B : Table (Set b) n} →
       GTable n (λ i → REL (A i) (B i) ℓ) → IRel {I = Fin n} A B ℓ
  PW _≈_ A B = {!∀ i → _≈_ i A B !}

-}

{-
  -------------------------
  -- Relation properties --
  -------------------------

  -- Pointwise properties
  module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where
  
   reflexive : _≡_ ⇒ _~_ → ∀ {n} → _≡_ ⇒ Pointwise _~_ {n}
   reflexive reflexive ≡-refl i = reflexive ≡-refl

   refl : Reflexive _~_ → ∀ {n} → Reflexive (Pointwise _~_ {n})
   refl reflexive i = reflexive

   sym : Symmetric _~_ → ∀ {n} → Symmetric (Pointwise _~_ {n})
   sym sym t~s i = sym (t~s i)

   trans : Transitive _~_ → ∀ {n} → Transitive (Pointwise _~_ {n})
   trans trans t~s s~r i = trans (t~s i) (s~r i)

   dec : Decidable _~_ → ∀ {n} → Decidable (Pointwise _~_ {n})
   dec dec t s = all? (λ i → dec (t i) (s i))

   isEquivalence : IsEquivalence _~_ → ∀ {n} → IsEquivalence (Pointwise _~_ {n})
   isEquivalence isEq = record
     { refl  = refl (IsEquivalence.refl isEq)
     ; sym   = sym (IsEquivalence.sym isEq)
     ; trans = trans (IsEquivalence.trans isEq)
     }

   isDecEquivalence : IsDecEquivalence _~_ →
                        ∀ {n} → IsDecEquivalence (Pointwise _~_ {n})
   isDecEquivalence isDecEq = record
     { isEquivalence = isEquivalence (IsDecEquivalence.isEquivalence isDecEq)
     ; _≟_           = dec (IsDecEquivalence._≟_ isDecEq)
     }

-}

  postulate setoid : ∀ {a ℓ n} → Table (Setoid a ℓ) n → ℕ → Setoid a ℓ
  {-
  setoid S n = record
    { isEquivalence = isEquivalence (Setoid.isEquivalence S) {n}
    }

  decSetoid : ∀ {a ℓ} → DecSetoid a ℓ → ℕ → DecSetoid a ℓ
  decSetoid DS n = record
    { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence DS) {n}
    }
  -}
