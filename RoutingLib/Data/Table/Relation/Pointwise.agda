open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (all?)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Table

module RoutingLib.Data.Table.Relation.Pointwise where

  Pointwise : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ →
           ∀ {n} → REL (Table A n) (Table B n) ℓ
  Pointwise _~_ A B = ∀ i → A i ~ B i


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

  setoid : ∀ {a ℓ} → Setoid a ℓ → ℕ → Setoid a ℓ
  setoid S n = record
    { isEquivalence = isEquivalence (Setoid.isEquivalence S) {n}
    }

  decSetoid : ∀ {a ℓ} → DecSetoid a ℓ → ℕ → DecSetoid a ℓ
  decSetoid DS n = record
    { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence DS) {n}
    }



  -------------------------
  -- Function properties --
  -------------------------

  zipWith-cong : ∀ {a b c d e f ℓ₁ ℓ₂ ℓ₃}
                 {A : Set a} {B : Set b} {C : Set c}
                 {D : Set d} {E : Set e} {F : Set f}
                 {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂} {_~₃_ : REL E F ℓ₃} →
                 ∀ {f : A → B → E} {g : C → D → F} →
                 (∀ {w x y z} → w ~₁ x → y ~₂ z → f w x ~₃ g y z) →
                 ∀ {n} {r : Table A n} {s : Table B n} {t : Table C n} {u : Table D n} →
                 Pointwise _~₁_ r s → Pointwise _~₂_ t u →
                 Pointwise _~₃_ (zipWith f r s) (zipWith g t u)
  zipWith-cong f-cong r~s t~u i = f-cong (r~s i) (t~u i)

  foldr-cong : ∀ {a b c d ℓ₁ ℓ₂}
               {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
               {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂} →
               ∀ {f : A → C → C} {g : B → D → D} →
               (∀ {w x y z} → w ~₁ x → y ~₂ z → f w y ~₂ g x z) →
               ∀ {d : C} {e : D} → d ~₂ e →
               ∀ {n} {s : Table A n} {t : Table B n} → Pointwise _~₁_ s t →
               foldr f d s ~₂ foldr g e t
  foldr-cong fg-cong d~e {zero}  s~t = d~e
  foldr-cong fg-cong d~e {suc n} s~t = fg-cong (s~t fzero) (foldr-cong (λ {w x y z} → fg-cong {w} {x} {y} {z}) d~e (s~t ∘ fsuc))

  foldr⁺-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
                {_•_ : Op₂ A} {_◦_ : Op₂ B} →
                (∀ {w x y z} → w ~ x → y ~ z → (w • y) ~ (x ◦ z)) →
                ∀ {n} {s : Table A (suc n)} {t : Table B (suc n)} →
                Pointwise _~_ s t → foldr⁺ _•_ s ~ foldr⁺ _◦_ t
  foldr⁺-cong •◦-cong s~t = foldr-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (s~t fzero) (s~t ∘ fsuc)
