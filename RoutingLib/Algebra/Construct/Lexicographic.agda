

module RoutingLib.Algebra.Construct.Lexicographic where

open import Algebra.FunctionProperties
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Function
open import RoutingLib.Algebra.FunctionProperties

module _ {a b ℓ} {A : Set a} {B : Set b} {_≈_ : Rel A ℓ}
         (_≟_ : Decidable _≈_) (_•_ : Op₂ A) (_◦_ : Op₂ B) where

  Lex : Op₂ (A × B)
  Lex (a , x) (b , y) with (a • b) ≟ a | (a • b) ≟ b
  ... | yes _ | no  _ = (a , x)
  ... | no  _ | yes _ = (b , y)
  ... | _     | _     = (a • b , x ◦ y)


module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel B ℓ₂}
         (_≟_ : Decidable _≈₁_) (_•_ : Op₂ A) (_◦_ : Op₂ B) where

  
  private
  
    infix 4 _≈ₓ_
    infix 7 _⊕_
  
    _⊕_ : Op₂ (A × B)
    _⊕_ = Lex _≟_ _•_ _◦_

    _≈ₓ_ : Rel (A × B) (ℓ₁ ⊔ ℓ₂)
    _≈ₓ_ = Pointwise _≈₁_ _≈₂_


  postulate assoc : Reflexive _≈₁_ → Reflexive _≈₂_ → Transitive _≈₁_ →
                    Associative _≈₁_ _•_ → Associative _≈₂_ _◦_ → Associative _≈ₓ_ _⊕_
  {-
  assoc refl₁ refl₂ trans₁ •-assoc ◦-assoc (a , x) (b , y) (c , z) = associative
    where
    associative : ((a , x) ⊕ (b , y)) ⊕ (c , z) ≈ₓ (a , x) ⊕ ((b , y) ⊕ (c , z))
    associative with (a • b) ≟ a | (a • b) ≟ b | (b • c) ≟ b | (b • c) ≟ c
    associative | no _  | no  _ | no  _ | no  _ = {!!}
    associative | no _  | no  _ | no  _ | yes _ = {!!}
    associative | no _  | no  _ | yes _ | no  _ = {!!}
    associative | no _  | no  _ | yes _ | yes _ = {!!}
    associative | no _  | yes _ | no  _ | no  _ = {!!}
    associative | no _  | yes _ | no  _ | yes _ = {!!}
    associative | no _  | yes _ | yes _ | no  _ = {!!}
    associative | no _  | yes _ | yes _ | yes _ = {!!}
    associative | yes _ | no  _ | no  _ | no  _ = {!!}
    associative | yes _ | no  _ | no  _ | yes _ = refl₁ , refl₂
    associative | yes _ | no  _ | yes _ | no  _ = {!!}
    associative | yes _ | no  _ | yes _ | yes _ = {!!}
    associative | yes _ | yes _ | no  _ | no  _ = {!!}
    associative | yes _ | yes _ | no  _ | yes _ = {!!}
    associative | yes _ | yes _ | yes _ | no  _ = {!!}
    associative | yes _ | yes _ | yes _ | yes _ = {!!}
      with ((a • b) • c) ≟ (a • b) | ((a • b) • c) ≟ c | (a • (b • c)) ≟ a | (a • (b • c)) ≟ (b • c)
    ... | no a∙b∙c≉a∙b  | _ | _ | _     = contradiction (trans₁ (•-assoc a b c) {!!}) a∙b∙c≉a∙b
    ... | _  | no a∙b∙c≉a∙c | _ | _     = contradiction (trans₁ {!!} {!!}) a∙b∙c≉a∙c
    ... | _  | _  | no a∙b∙c≉a  | _     = contradiction (trans₁ {!!} {!!}) a∙b∙c≉a
    ... | _  | _  | _ | no  a∙b∙c≉b∙c   = contradiction (trans₁ {!sym₁ (•-assoc a b c)!} {!!}) a∙b∙c≉b∙c
    ... | yes _ | yes _ | yes _ | yes _  = •-assoc a b c , ◦-assoc x y z
  -}

  comm : Reflexive _≈₁_ → Reflexive _≈₂_ → Transitive _≈₁_ →
         Commutative _≈₁_ _•_ → Commutative _≈₂_ _◦_ → Commutative _≈ₓ_ _⊕_
  comm refl₁ refl₂ trans₁ •-comm ◦-comm (a , x) (b , y)
    with (a • b) ≟ a | (b • a) ≟ a | (a • b) ≟ b | (b • a) ≟ b 
  ... | yes a•b≈a | no  b•a≉a | _         | _         = contradiction (trans₁ (•-comm b a) a•b≈a) b•a≉a
  ... | no  a•b≉a | yes b•a≈a | _         | _         = contradiction (trans₁ (•-comm a b) b•a≈a) a•b≉a
  ... | _         | _         | yes a•b≈b | no  b•a≉a = contradiction (trans₁ (•-comm b a) a•b≈b) b•a≉a
  ... | _         | _         | no  a•b≉b | yes b•a≈a = contradiction (trans₁ (•-comm a b) b•a≈a) a•b≉b
  ... | no  _     | no  _     | no  _     | no  _      = •-comm a b , ◦-comm x y
  ... | no  _     | no  _     | yes _     | yes _      = refl₁      , refl₂
  ... | yes _     | yes _     | no  _     | no  _      = refl₁      , refl₂
  ... | yes _     | yes _     | yes  _    | yes _      = •-comm a b , ◦-comm x y

  sel : Reflexive _≈₁_ → Reflexive _≈₂_ →
        Selective _≈₁_ _•_ → Selective _≈₂_ _◦_ → Selective _≈ₓ_ _⊕_
  sel refl₁ refl₂ •-sel ◦-sel (a , x) (b , y) with (a • b) ≟ a | (a • b) ≟ b
  ... | no  a•b≉a | no  a•b≉b  = [ contradiction ◌ a•b≉a , contradiction ◌ a•b≉b ] (•-sel a b)
  ... | yes _     | no  _      = inj₁ (refl₁ , refl₂)
  ... | no  _     | yes _      = inj₂ (refl₁ , refl₂)
  ... | yes a•b≈a | yes a•b≈b  with ◦-sel x y
  ...   | inj₁ x◦y≈x = inj₁ (a•b≈a , x◦y≈x)
  ...   | inj₂ x◦y≈y = inj₂ (a•b≈b , x◦y≈y)

  zeroʳ : Reflexive _≈₁_ → Reflexive _≈₂_ → 
          ∀ {0₁ 0₂} → RightZero _≈₁_ 0₁ _•_ → RightZero _≈₂_ 0₂ _◦_ →
          RightZero _≈ₓ_ (0₁ , 0₂) _⊕_
  zeroʳ refl₁ refl₂ {0₁} zeroʳ₁ zeroʳ₂ (x , a) with (x • 0₁) ≟ x | (x • 0₁) ≟ 0₁
  ... | _     | no x•0≉0 = contradiction (zeroʳ₁ x) x•0≉0
  ... | no  _ | yes _    = refl₁ , refl₂
  ... | yes _ | yes _    = (zeroʳ₁ x) , (zeroʳ₂ a)

  cong : Symmetric _≈₁_ → Transitive _≈₁_ →
         Congruent₂ _≈₁_ _•_ → Congruent₂ _≈₂_ _◦_ → Congruent₂ _≈ₓ_ _⊕_
  cong sym₁ trans₁ •-cong ◦-cong {a , w} {b , x} {c , y} {d , z} (a≈b , w≈x) (c≈d , y≈z)
    with (a • c) ≟ a | (b • d) ≟ b | (a • c) ≟ c | (b • d) ≟ d
  ... | yes a•c≈a | no  b•d≉b | _         | _         = contradiction (trans₁ (trans₁ (•-cong (sym₁ a≈b) (sym₁ c≈d)) a•c≈a) a≈b) b•d≉b
  ... | no  a•c≉a | yes b•d≈b | _         | _         = contradiction (trans₁ (trans₁ (•-cong a≈b c≈d) b•d≈b) (sym₁ a≈b)) a•c≉a
  ... | _         | _         | yes a•c≈c | no  b•d≉d = contradiction (trans₁ (trans₁ (•-cong (sym₁ a≈b) (sym₁ c≈d)) a•c≈c) c≈d) b•d≉d
  ... | _         | _         | no  a•c≉c | yes b•d≈d = contradiction (trans₁ (trans₁ (•-cong a≈b c≈d) b•d≈d) (sym₁ c≈d)) a•c≉c
  ... | no  _     | no  _     | no  _     | no  _      = •-cong a≈b c≈d , ◦-cong w≈x y≈z
  ... | no  _     | no  _     | yes _     | yes _      = c≈d , y≈z
  ... | yes _     | yes _     | no  _     | no  _      = a≈b , w≈x
  ... | yes _     | yes _     | yes  _    | yes _      = •-cong a≈b c≈d , ◦-cong w≈x y≈z


  opLex-proj₁ : Reflexive _≈₁_ → Symmetric _≈₁_ → ∀ x y → proj₁ (x ⊕ y) ≈₁ ((proj₁ x) • (proj₁ y))
  opLex-proj₁ refl₁ sym₁ (a , x) (b , y) with (a • b) ≟ a | (a • b) ≟ b
  ... | yes p | yes p₁ = refl₁
  ... | yes p | no ¬p  = sym₁ p
  ... | no ¬p | yes p  = sym₁ p
  ... | no ¬p | no ¬p₁ = refl₁
