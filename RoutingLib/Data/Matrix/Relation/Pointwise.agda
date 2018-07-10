open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (all?)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Data.Matrix
import RoutingLib.Data.Table.Relation.Pointwise as Table

module RoutingLib.Data.Matrix.Relation.Pointwise where

  Pointwise : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ →
           ∀ {m n} → REL (Matrix A m n) (Matrix B m n) ℓ
  Pointwise _~_ M N = ∀ i j → M i j ~ N i j

  -------------------------
  -- Relation properties --
  -------------------------

  -- Pointwise properties
  module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

    abstract

      reflexive : _≡_ ⇒ _~_ → ∀ {m n} → _≡_ ⇒ Pointwise _~_ {m} {n}
      reflexive reflexive ≡-refl = Table.reflexive (Table.reflexive reflexive) ≡-refl

      refl : Reflexive _~_ → ∀ {m n} → Reflexive (Pointwise _~_ {m} {n})
      refl reflexive i j = reflexive

      sym : Symmetric _~_ → ∀ {m n} → Symmetric (Pointwise _~_ {m} {n})
      sym sym M~N i j = sym (M~N i j)

      trans : Transitive _~_ → ∀ {m n} → Transitive (Pointwise _~_ {m} {n})
      trans trans M~N N~P i j = trans (M~N i j) (N~P i j)

      dec : Decidable _~_ → ∀ {m n} → Decidable (Pointwise _~_ {m} {n})
      dec dec M N = all? (λ i → all? (λ j → dec (M i j) (N i j)))

      isEquivalence : IsEquivalence _~_ → ∀ {m n} → IsEquivalence (Pointwise _~_ {m} {n})
      isEquivalence isEq = record
        { refl  = refl  (IsEquivalence.refl  isEq)
        ; sym   = sym   (IsEquivalence.sym   isEq)
        ; trans = trans (IsEquivalence.trans isEq)
        }

      isDecEquivalence : IsDecEquivalence _~_ →
                         ∀ {m} {n} → IsDecEquivalence (Pointwise _~_ {m} {n})
      isDecEquivalence isDecEq = record
        { isEquivalence = isEquivalence (IsDecEquivalence.isEquivalence isDecEq)
        ; _≟_           = dec           (IsDecEquivalence._≟_           isDecEq)
        }

  setoid : ∀ {a ℓ} → Setoid a ℓ → ℕ → ℕ → Setoid a ℓ
  setoid S m n = record
    { Carrier       = Matrix (Setoid.Carrier S) m n
    ; _≈_           = Pointwise (Setoid._≈_ S)
    ; isEquivalence = isEquivalence (Setoid.isEquivalence S)
    }

  decSetoid : ∀ {a ℓ} → DecSetoid a ℓ → ℕ → ℕ → DecSetoid a ℓ
  decSetoid DS m n = record
    { Carrier          = Matrix (DecSetoid.Carrier DS) m n
    ; _≈_              = Pointwise (DecSetoid._≈_ DS)
    ; isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence DS)
    }

  -------------------------
  -- Function properties --
  -------------------------

  zipWith-cong : ∀ {a b c d e f ℓ₁ ℓ₂ ℓ₃}
                 {A : Set a} {B : Set b} {C : Set c}
                 {D : Set d} {E : Set e} {F : Set f}
                 (_~₁_ : REL A B ℓ₁) (_~₂_ : REL C D ℓ₂) (_~₃_ : REL E F ℓ₃) →
                 ∀ {f g} → (∀ {x y u v} → x ~₁ y → u ~₂ v → f x u ~₃ g y v) →
                 ∀ {m n} {r : Matrix A m n} {s t u} →
                 Pointwise _~₁_ r s → Pointwise _~₂_ t u →
                 Pointwise _~₃_ (zipWith f r t) (zipWith g s u)
  zipWith-cong _ _ _ f-cong r~s t~u i j = f-cong (r~s i j) (t~u i j)

  fold-cong : ∀ {a b c d ℓ₁ ℓ₂}
               {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
               {_~₁_ : REL A B ℓ₁} {_~₂_ : REL C D ℓ₂} →
               ∀ {f : A → C → C} {g : B → D → D} →
               (∀ {w x y z} → w ~₁ x → y ~₂ z → f w y ~₂ g x z) →
               ∀ {d : C} {e : D} → d ~₂ e →
               ∀ {m n} {M : Matrix A m n} {N : Matrix B m n} → Pointwise _~₁_ M N →
               fold f d M ~₂ fold g e N
  fold-cong fg-cong d~e {zero}  M~N = d~e
  fold-cong fg-cong d~e {suc n} M~N = Table.foldr-cong (λ {w x y z} → fg-cong {w} {x} {y} {z}) (fold-cong (λ {w x y z} → fg-cong {w} {x} {y} {z}) d~e (M~N ∘ fsuc)) (M~N fzero)

  fold⁺-cong : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ}
                {_•_ : Op₂ A} {_◦_ : Op₂ B} →
                (∀ {w x y z} → w ~ x → y ~ z → (w • y) ~ (x ◦ z)) →
                ∀ {m n} {M : Matrix A (suc m) (suc n)} {N : Matrix B (suc m) (suc n)} →
                Pointwise _~_ M N → fold⁺ _•_ M ~ fold⁺ _◦_ N
  fold⁺-cong •◦-cong {zero}  M~N = Table.foldr⁺-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (M~N fzero)
  fold⁺-cong •◦-cong {suc m} M~N = •◦-cong (Table.foldr⁺-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (M~N fzero)) (fold⁺-cong (λ {w x y z} → •◦-cong {w} {x} {y} {z}) (M~N ∘ fsuc))
