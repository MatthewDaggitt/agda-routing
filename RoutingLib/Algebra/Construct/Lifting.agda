open import Algebra.FunctionProperties
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)
open import Level using (_⊔_)
open import Function using (id; _on_)
open import Function.Injection using (Injection)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Algebra.Construct.Lifting
  {a b ℓ} {A : Set a} {B : Set b} {_•_ : Op₂ B}
  (_≈ᵇ_ : Rel B ℓ) (•-sel : Selective _≈ᵇ_ _•_) (f : A → B)
  where

Lift : Op₂ A
Lift x y with •-sel (f x) (f y)
... | inj₁ _ = x
... | inj₂ _ = y

sel : Selective _≡_ Lift
sel x y with •-sel (f x) (f y)
... | inj₁ _ = inj₁ refl
... | inj₂ _ = inj₂ refl

presᵒ : ∀ {p} {P : Pred A p} →
        (∀ {x y} → P x → (f x • f y) ≈ᵇ f y → P y) →
        (∀ {x y} → P y → (f x • f y) ≈ᵇ f x → P x) →
        Lift Preservesᵒ P
presᵒ left right x y (inj₁ px) with •-sel (f x) (f y)
... | inj₁ _        = px
... | inj₂ fx•fy≈fx = left px fx•fy≈fx
presᵒ left right x y (inj₂ py) with •-sel (f x) (f y)
... | inj₁ fx•fy≈fy = right py fx•fy≈fy
... | inj₂ _ = py

presʳ : ∀ {p} {P : Pred A p} →
        (∀ {x y} → P y → (f x • f y) ≈ᵇ f x → P x) →
        Lift Preservesʳ P
presʳ right x {y} Py with •-sel (f x) (f y)
... | inj₁ fx•fy≈fx = right Py fx•fy≈fx
... | inj₂ fx•fy≈fy = Py

presᵇ : ∀ {p} (P : Pred A p) → Lift Preservesᵇ P
presᵇ P {x} {y} Px Py with •-sel (f x) (f y)
... | inj₁ _ = Px
... | inj₂ _ = Py

forcesᵇ : ∀ {p} {P : Pred A p} →
          (∀ {x y} → P x → (f x • f y) ≈ᵇ f x → P y) →
          (∀ {x y} → P y → (f x • f y) ≈ᵇ f y → P x) →
          Lift Forcesᵇ P
forcesᵇ presˡ presʳ x y P[x•y] with •-sel (f x) (f y)
... | inj₁ fx•fy≈fx = P[x•y] , presˡ P[x•y] fx•fy≈fx
... | inj₂ fx•fy≈fy = presʳ P[x•y] fx•fy≈fy , P[x•y]


{-
  module _ {ℓ} {f : A → B} {_≈ᵇ_ : Rel B ℓ} {•-sel : Selective _≈ᵇ_ _•_} where

    --open EqReasoning S

    _◦_ : Op₂ A
    _◦_ = Lift _≈ᵇ_ •-sel f

    distrib : ∀ x y → ((f x) • (f y)) ≈ᵇ f (x ◦ y)
    distrib x y with •-sel (f x) (f y)
    ... | inj₁ fx•fy≈fx = fx•fy≈fx
    ... | inj₂ fx•fy≈fy = fx•fy≈fy


    {-
    presᵒ : ∀ {p} → (P : Pred A p) → (∀ {x y} → (f x • f y) ≈ᵇ f x → P y → P x) → _◦_ Preservesᵒ P
    presᵒ P impl a b Pa⊎Pb with •-sel (f a) (f b)
    ... | inj₁ fa•fb≈fa = [ id , impl fa•fb≈fa ] Pa⊎Pb
    ... | inj₂ fa•fb≈fb = [ impl {!!} , id ] Pa⊎Pb
    -}

    module _ {ℓ₂} {_≈ᵃ_ : Rel A ℓ₂} where

      {-
      private

        Injective : (f : A → B) → Set _
        Injective = ∀ {x y} → f x ≈ᵇ f y → x ≈ᵃ y

      assoc : Congruent₂ _≈ᵇ_ _•_ → Injective → Associative _≈ᵇ_ _•_ →
              Associative _≈ᵃ_ _◦_
      assoc •-cong injective •-assoc x y z = injective (begin
        f ((x ◦ y) ◦ z)   ≈⟨ distrib (x ◦ y) z ⟩
        f (x ◦ y) • f z   ≈⟨ •-cong (distrib x y) refl ⟩
        (f x • f y) • f z ≈⟨ •-assoc (f x) (f y) (f z) ⟩
        f x • (f y • f z) ≈⟨ •-cong refl (sym (distrib y z)) ⟩
        f x • f (y ◦ z)   ≈⟨ sym (distrib x (y ◦ z)) ⟩
        f (x ◦ (y ◦ z))   ∎)

      comm : Injective → Commutative _≈ᵇ_ _•_ → Commutative _≈ᵃ_ _◦_
      comm injective •-comm x y = injective (begin
        f (x ◦ y) ≈⟨ distrib x y ⟩
        f x • f y ≈⟨ •-comm (f x) (f y) ⟩
        f y • f x ≈⟨ sym (distrib y x) ⟩
        f (y ◦ x) ∎)
      -}

  -}

{-
  cong : Injective → Congruent₁ _≈ᵇ_ _•_ → Congruent₂ _≈ᵃ_ _◦_
  cong injective •-cong {x} {y} {u} {v} x≈y u≈v with •-sel (f x) (f u) | •-sel (f y) (f v)
  ... | inj₁ fx•fu≈fx | inj₁ fy•fv≈fy = x≈y
  ... | inj₂ fx•fu≈fu | inj₂ fy•fv≈fv = u≈v
  ... | inj₁ fx•fu≈fx | inj₂ fy•fv≈fv = injective (begin
    f x       ≈⟨ sym fx•fu≈fx ⟩
    f x • f u ≈⟨ •-cong (f-cong x≈y) (f-cong u≈v) ⟩
    f y • f v ≈⟨ fy•fv≈fv ⟩
    f v ∎)
  ... | inj₂ fx•fu≈fu | inj₁ fy•fv≈fy = injective (begin
    f u       ≈⟨ B.sym fx•fu≈fu ⟩
    f x • f u ≈⟨ •-cong (f-cong x≈y) (f-cong u≈v) ⟩
    f y • f v ≈⟨ fy•fv≈fy ⟩
    f y ∎)
-}
