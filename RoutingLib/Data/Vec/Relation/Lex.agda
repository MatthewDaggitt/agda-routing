open import Data.Nat hiding (_≤?_; _≟_; compare)
open import Data.Vec
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; isEquivalence)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Vec.Properties using (≡-dec)

module RoutingLib.Data.Vec.Relation.Lex {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

  data Lex : ∀ {n} → Rel (Vec A n) ℓ where
    base : Lex [] []
    here : ∀ {n x y} {xs ys : Vec A n} → x < y → Lex (x ∷ xs) (y ∷ ys)
    next : ∀ {n x} {xs ys : Vec A n} → Lex xs ys → Lex (x ∷ xs) (x ∷ ys)

  ≤-refl : ∀ {n} → Reflexive (Lex {n})
  ≤-refl {x = []}     = base
  ≤-refl {x = x ∷ xs} = next ≤-refl

  ≤-reflexive : ∀ {n} → _≡_ ⇒ (Lex {n})
  ≤-reflexive refl = ≤-refl

  ≤-trans : Transitive _<_ → ∀ {n} → Transitive (Lex {n})
  ≤-trans trans base         base         = base
  ≤-trans trans (here x<y)   (here y<z)   = here (trans x<y y<z)
  ≤-trans trans (here x<y)   (next ys≤xs) = here x<y
  ≤-trans trans (next xs≤ys) (here y<z)   = here y<z
  ≤-trans trans (next xs≤ys) (next ys≤zs) = next (≤-trans trans xs≤ys ys≤zs)

  ≤-antisym : Asymmetric _<_ → ∀ {n} → Antisymmetric _≡_ (Lex {n})
  ≤-antisym asym base         base         = refl
  ≤-antisym asym (here x<y)   (here y<x)   = contradiction x<y (asym y<x)
  ≤-antisym asym (here x<x)   (next ys≤xs) = contradiction x<x (asym x<x)
  ≤-antisym asym (next xs≤ys) (here y<y)   = contradiction y<y (asym y<y)
  ≤-antisym asym (next xs≤ys) (next ys≤xs) = cong (_ ∷_) (≤-antisym asym xs≤ys ys≤xs)

  ≤-total : Trichotomous _≡_ _<_ → ∀ {n} → Total (Lex {n})
  ≤-total cmp []       []       = inj₁ base
  ≤-total cmp (x ∷ xs) (y ∷ ys) with cmp x y
  ... | tri< x<y _ _ = inj₁ (here x<y)
  ... | tri> _ _ y<x = inj₂ (here y<x)
  ... | tri≈ _ refl _ with ≤-total cmp xs ys
  ...   | inj₁ xs≤ys = inj₁ (next xs≤ys)
  ...   | inj₂ ys≤xs = inj₂ (next ys≤xs)

  ≤-dec : Trichotomous _≡_ _<_ → ∀ {n} → Decidable (Lex {n})
  ≤-dec tri []       []       = yes base
  ≤-dec tri (x ∷ xs) (y ∷ ys) with tri x y
  ... | tri< x<y _   _ = yes (here x<y)
  ... | tri> x≮y x≢x _ = no λ
    { (here x<y)   → x≮y x<y
    ; (next xs≤ys) → x≢x refl
    }
  ... | tri≈ x≮y refl _ with ≤-dec tri xs ys
  ...   | yes xs≤ys = yes (next xs≤ys)
  ...   | no  xs≰ys = no λ
    { (here x<y)   → x≮y x<y
    ; (next xs≤ys) → xs≰ys xs≤ys
    }

  ≤-minimum : Decidable _≡_ → ∀ {⊥} → (∀ {x} → x ≢ ⊥ → ⊥ < x) → ∀ {n} → Minimum (Lex {n}) (replicate ⊥)
  ≤-minimum dec {⊥} bot []       = base
  ≤-minimum dec {⊥} bot (x ∷ xs) with dec x ⊥
  ... | yes refl = next (≤-minimum dec bot xs)
  ... | no  x≢⊥  = here (bot x≢⊥)

  ≤-isDecTotalOrder : IsStrictTotalOrder _≡_ _<_ → ∀ {n} → IsDecTotalOrder _≡_ (Lex {n})
  ≤-isDecTotalOrder order = record
    { isTotalOrder = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = isEquivalence
          ; reflexive     = ≤-reflexive
          ; trans         = ≤-trans trans
          }
        ; antisym    = ≤-antisym asym
        }
      ; total        = ≤-total compare
      }
    ; _≟_          = ≡-dec _≟_
    ; _≤?_         = ≤-dec compare
    }
    where open IsStrictTotalOrder order hiding (isEquivalence)
