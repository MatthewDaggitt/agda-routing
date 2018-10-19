open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Dec using (all?)
open import Data.Fin.Subset using (Subset; _∉_; inside; outside; ∣_∣)
open import Data.Vec using ([]; _∷_; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary as B
  using (Setoid; DecSetoid; IsEquivalence; IsDecEquivalence; REL; Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Table
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Data.Fin.Subset.Properties using (∉-contract)

module RoutingLib.Data.Table.Relation.Pointwise where

------------------------------------------------------------------------------
-- Definition

Pointwise : ∀ {a b ℓ} {A : Set a} {B : Set b} →
            REL A B ℓ → IREL (Table A) (Table B) ℓ
Pointwise _~_ A B = ∀ i → A i ~ B i

------------------------------------------------------------------------------
-- Relational properties

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

  reflexive : _≡_ B.⇒ _~_ → ∀ {n} → _≡_ B.⇒ Pointwise _~_ {n}
  reflexive reflexive ≡-refl i = reflexive ≡-refl

  refl : B.Reflexive _~_ → Reflexive (Table A) (Pointwise _~_)
  refl reflexive i = reflexive

  sym : B.Symmetric _~_ → Symmetric (Table A) (Pointwise _~_)
  sym sym t~s i = sym (t~s i)

  trans : B.Transitive _~_ → Transitive (Table A) (Pointwise _~_)
  trans trans t~s s~r i = trans (t~s i) (s~r i)

  dec : B.Decidable _~_ → Decidable (Table A) (Pointwise _~_)
  dec dec t s = all? (λ i → dec (t i) (s i))

  isEquivalence : IsEquivalence _~_ → ∀ {n} → IsEquivalence (Pointwise _~_ {n})
  isEquivalence isEq = record
    { refl  = refl  Eq.refl
    ; sym   = sym   Eq.sym
    ; trans = trans Eq.trans
    }
    where module Eq = IsEquivalence isEq

  isIndexedEquivalence : IsEquivalence _~_ → IsIndexedEquivalence (Table A) (Pointwise _~_)
  isIndexedEquivalence isEq = record
    { reflᵢ  = refl  Eq.refl
    ; symᵢ   = sym   Eq.sym
    ; transᵢ = trans Eq.trans
    }
    where module Eq = IsEquivalence isEq

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


------------------------------------------------------------------------------
-- zipWith

module _ {a b c d e f} {ℓ₁ ℓ₂ ℓ₃}
         {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f}
         {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂} {_~₃_ : REL E F ℓ₃}
         {f : A → B → E} {g : C → D → F}
         where
         
  zipWith-cong : (∀ {w x y z} → w ~₁ x → y ~₂ z → f w x ~₃ g y z) →
                 ∀ {n} {r : Table A n} {s : Table B n} {t : Table C n} {u : Table D n} →
                 Pointwise _~₁_ r s → Pointwise _~₂_ t u →
                 Pointwise _~₃_ (zipWith f r s) (zipWith g t u)
  zipWith-cong f-cong r~s t~u i = f-cong (r~s i) (t~u i)


------------------------------------------------------------------------------
-- foldr

module _ {a b c d} {ℓ₁ ℓ₂}
         {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂}
         {f : A → C → C} {g : B → D → D}
         where
         
  foldr-cong : (∀ {w x y z} → w ~₁ x → y ~₂ z → f w y ~₂ g x z) →
               ∀ {d : C} {e : D} → d ~₂ e →
               ∀ {n} {s : Table A n} {t : Table B n} → Pointwise _~₁_ s t →
               foldr f d s ~₂ foldr g e t
  foldr-cong fg-cong d~e {zero}  s~t = d~e
  foldr-cong fg-cong d~e {suc n} s~t = fg-cong (s~t zero) (foldr-cong (λ {w x y z} → fg-cong {w} {x} {y} {z}) d~e (s~t ∘ suc))
  
module _ where

  foldr⁺-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
                {_•_ : Op₂ A} {_◦_ : Op₂ B} →
                (∀ {w x y z} → w ~ x → y ~ z → (w • y) ~ (x ◦ z)) →
                ∀ {n} {s : Table A (suc n)} {t : Table B (suc n)} →
                Pointwise _~_ s t → foldr⁺ _•_ s ~ foldr⁺ _◦_ t
  foldr⁺-cong •◦-cong {zero}  s~t = s~t zero
  foldr⁺-cong •◦-cong {suc n} s~t = •◦-cong (s~t zero) (foldr⁺-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (s~t ∘ suc))

------------------------------------------------------------------------------
-- strip

module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} (~-refl : B.Reflexive _~_) where
  
  grow-strip : ∀ {n} (p : Subset n) (t : Table A n) (f : Table A n) →
               (∀ {i} → i ∉ p → t i ~ f i) → Pointwise _~_ (grow p t (strip p f)) f
  grow-strip []            t f ∉⇒~ ()
  grow-strip (outside ∷ p) t f ∉⇒~ zero    = ∉⇒~ λ()
  grow-strip (outside ∷ p) t f ∉⇒~ (suc i) = grow-strip p (t ∘ suc) (f ∘ suc) (λ i∉p → ∉⇒~ (∉-contract i∉p)) i
  grow-strip (inside ∷ p)  t f ∉⇒~ zero    = ~-refl
  grow-strip (inside ∷ p)  t f ∉⇒~ (suc i) = grow-strip p (t ∘ suc) (f ∘ suc) (λ i∉p → ∉⇒~ (∉-contract i∉p)) i

  strip-grow : ∀ {n} (p : Subset n) (t : Table A n) (f : Table A ∣ p ∣) →
               Pointwise _~_ (strip p (grow p t f)) f
  strip-grow []            t f ()
  strip-grow (outside ∷ p) t f i       = strip-grow p (t ∘ suc) f i
  strip-grow (inside ∷ p)  t f zero    = ~-refl
  strip-grow (inside ∷ p)  t f (suc i) = strip-grow p (t ∘ suc) (f ∘ suc) i
