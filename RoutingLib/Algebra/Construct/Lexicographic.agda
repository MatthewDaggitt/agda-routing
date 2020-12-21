

module RoutingLib.Algebra.Construct.Lexicographic where

open import Algebra
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.Reasoning.Setoid as EqReasoning

open import RoutingLib.Relation.Nullary.Negation

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

module _ {_≈_ : Rel A ℓ} (_≟_ : Decidable _≈_) (_•_ : Op₂ A) (_◦_ : Op₂ B) where

  -- Note: for non-selective • the result in the no+no case must be
  -- the identity of B (for associativity to hold).
  Lex₂ : A → A → B → B → B
  Lex₂ a b x y with (a • b) ≟ a | (a • b) ≟ b
  ... | yes _ | no  _ = x
  ... | no  _ | yes _ = y
  ... |     _ |     _ = x ◦ y

  Lex : Op₂ (A × B)
  Lex (a , x) (b , y) = (a • b , Lex₂ a b x y)

------------------------------------------------------------------------
-- Properties

module _ (∙-magma : Magma a ℓ₁) (◦-magma : Magma b ℓ₂)
  (_≟₁_ : Decidable (Magma._≈_ ∙-magma))
  where

  open Magma ∙-magma public
    using () renaming
    ( Carrier       to C₁
    ; _∙_           to _•_
    ; ∙-cong        to •-cong
    ; _≈_           to _≈₁_
    ; refl          to ≈₁-refl
    ; sym           to ≈₁-sym
    ; trans         to ≈₁-trans
    ; setoid        to S₁
    )

  open Magma ◦-magma
    renaming
    ( Carrier       to C₂
    ; _≈_           to _≈₂_
    ; _∙_           to _◦_
    ; ∙-cong        to ◦-cong
    ; refl          to ≈₂-refl
    ; sym           to ≈₂-sym
    ; trans         to ≈₂-trans
    ; setoid        to S₂
    )

  private
    infix 7 _⊕_
    infix 4 _≈ₓ_ _≉₁_

    _≉₁_ : Rel C₁ _
    x ≉₁ y = ¬ (x ≈₁ y)

    _⊕_ : Op₂ (C₁ × C₂)
    _⊕_ = Lex _≟₁_ _•_ _◦_

    L₂ : C₁ → C₁ → C₂ → C₂ → C₂
    L₂ = Lex₂ _≟₁_ _•_ _◦_

    _≈ₓ_ : Rel (C₁ × C₂) _
    _≈ₓ_ = Pointwise _≈₁_ _≈₂_

    L₂-cong : ∀ {a₁ a₂ b₁ b₂ x₁ x₂ y₁ y₂} → a₁ ≈₁ a₂ → b₁ ≈₁ b₂ → x₁ ≈₂ x₂ → y₁ ≈₂ y₂ → L₂ a₁ b₁ x₁ y₁ ≈₂ L₂ a₂ b₂ x₂ y₂
    L₂-cong  {a₁} {a₂} {b₁} {b₂} a₁≈a₂ b₁≈b₂ x₁≈x₂ y₁≈y₂
      with (a₁ • b₁) ≟₁ a₁ | (a₁ • b₁) ≟₁ b₁ | (a₂ • b₂) ≟₁ a₂ | (a₂ • b₂) ≟₁ b₂
    ... | yes p | yes p₁ | yes p₂ | yes p₃ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | yes p | yes p₁ | no ¬p  | no ¬p₁ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | no ¬p | no ¬p₁ | yes p  | yes p₁ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | yes p | no ¬p  | yes p₁ | no ¬p₁ = x₁≈x₂
    ... | no ¬p | yes p  | no ¬p₁ | yes p₁ = y₁≈y₂
    ... | _     | yes p₁ | _      | no ¬p  = contradiction (≈₁-trans (≈₁-trans (≈₁-sym (•-cong a₁≈a₂ b₁≈b₂)) p₁) b₁≈b₂)  ¬p
    ... | yes p | _      | no ¬p  | _      = contradiction (≈₁-trans (≈₁-trans (≈₁-sym (•-cong a₁≈a₂ b₁≈b₂)) p) a₁≈a₂)   ¬p
    ... | _     | no ¬p  | _      | yes p₂ = contradiction (≈₁-trans (≈₁-trans (•-cong a₁≈a₂ b₁≈b₂) p₂) (≈₁-sym b₁≈b₂)) ¬p
    ... | no ¬p | _      | yes p  | _      = contradiction (≈₁-trans (≈₁-trans (•-cong a₁≈a₂ b₁≈b₂) p)  (≈₁-sym a₁≈a₂))  ¬p

    Lex₂-case₁ : ∀ {a b x y} → (a • b) ≈₁ a → (a • b) ≉₁ b → L₂ a b x y ≈₂ x
    Lex₂-case₁ {a} {b} {x} {y} ab=a ¬ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = contradiction p₁ ¬ab=b
    ... | yes p | no ¬p  = ≈₂-refl
    ... | no ¬p | yes p  = contradiction ab=a ¬p
    ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

    Lex₂-case₂ : ∀ {a b x y}  → (a • b) ≉₁ a → (a • b) ≈₁ b → L₂ a b x y ≈₂ y
    Lex₂-case₂ {a} {b} {x} {y} ¬ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = contradiction p ¬ab=a
    ... | yes p | no ¬p  = contradiction p ¬ab=a
    ... | no ¬p | yes p  = ≈₂-refl
    ... | no ¬p | no ¬p₁ = contradiction ab=b ¬p₁

    Lex₂-case₃ : ∀ {a b x y}  → (a • b) ≈₁ a → (a • b) ≈₁ b → L₂ a b x y ≈₂ (x ◦ y)
    Lex₂-case₃ {a} {b} {x} {y} ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = ≈₂-refl
    ... | yes p | no ¬p  = contradiction ab=b ¬p
    ... | no ¬p | yes p  = contradiction ab=a ¬p
    ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

    L₂-assoc : Associative _≈₁_ _•_ → Associative _≈₂_ _◦_ → Selective _≈₁_ _•_ → Commutative _≈₁_ _•_ →
               ∀ a b c x y z  → L₂ (a • b) c (L₂ a b x y) z  ≈₂ L₂ a (b • c) x (L₂ b c y z)
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z with (a • b) ≟₁ a | (a • b) ≟₁ b | (b • c) ≟₁ b | (b • c) ≟₁ c
    ... | yes ab=a | yes ab=b | yes bc=b | yes bc=c = prf
      where
      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x (y ◦ z)
      prf = begin
        L₂ (a • b) c (x ◦ y) z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
        L₂ b c (x ◦ y) z                 ≈⟨ Lex₂-case₃ bc=b bc=c  ⟩
        (x ◦ y) ◦ z                      ≈⟨ ◦-assoc x y z ⟩
        x ◦ (y ◦ z)                      ≈⟨ ≈₂-sym (Lex₂-case₃ ab=a ab=b) ⟩
        L₂ a b x (y ◦ z)                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl   ⟩
        L₂ a (b • c) x (y ◦ z)     ∎
        where open EqReasoning S₂

    ... | yes ab=a | yes ab=b | yes bc=b | no ¬bc=c = prf
      where
      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x y
      prf = begin
        L₂ (a • b) c (x ◦ y) z  ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
        L₂ b c (x ◦ y) z        ≈⟨ Lex₂-case₁ bc=b ¬bc=c ⟩
        x ◦ y                   ≈⟨ ≈₂-sym (Lex₂-case₃ ab=a ab=b) ⟩
        L₂ a b x y              ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl  ⟩
        L₂ a (b • c) x y        ∎
        where open EqReasoning S₂

    ... | yes ab=a | yes ab=b | no ¬bc=b | yes bc=c = prf
      where
      b=a : b ≈₁ a
      b=a = ≈₁-trans (≈₁-sym ab=b) ab=a

      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x z
      prf = begin
        L₂ (a • b) c (x ◦ y) z      ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
        L₂ b c (x ◦ y) z            ≈⟨ Lex₂-case₂ ¬bc=b bc=c ⟩
        z                           ≈⟨ ≈₂-sym (Lex₂-case₂ ¬bc=b bc=c) ⟩
        L₂ b c x z                  ≈⟨ L₂-cong b=a (≈₁-sym bc=c) ≈₂-refl ≈₂-refl ⟩
        L₂ a (b • c) x z            ∎
        where open EqReasoning S₂

    ... | yes ab=a | no ¬ab=b | yes bc=b | yes bc=c = prf
      where
      c=b : c ≈₁ b
      c=b = ≈₁-trans (≈₁-sym bc=c) bc=b

      prf : L₂ (a • b) c x z  ≈₂ L₂ a (b • c) x (y ◦ z)
      prf = begin
        L₂ (a • b) c x z           ≈⟨ L₂-cong ab=a c=b ≈₂-refl ≈₂-refl  ⟩
        L₂ a b x z                 ≈⟨ Lex₂-case₁ ab=a ¬ab=b ⟩
        x                          ≈⟨ ≈₂-sym (Lex₂-case₁ ab=a ¬ab=b) ⟩
        L₂ a b x (y ◦ z)           ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
        L₂ a (b • c) x (y ◦ z)     ∎
        where open EqReasoning S₂

    ... | yes ab=a | no ¬ab=b | yes bc=b | no ¬bc=c = prf
      where
      ac=a : (a • c) ≈₁ a
      ac=a = begin
        (a • c)            ≈⟨ •-cong (≈₁-sym ab=a) ≈₁-refl  ⟩
        (a • b) • c        ≈⟨ •-assoc a b c ⟩
        a • (b • c)        ≈⟨ •-cong ≈₁-refl bc=b ⟩
        a • b              ≈⟨ ab=a ⟩
        a                  ∎
        where open EqReasoning S₁

      ac=c->a=c : (a • c) ≈₁ c → a ≈₁ c
      ac=c->a=c ac=c = begin
        a                  ≈⟨ ≈₁-sym ab=a ⟩
        a • b              ≈⟨ •-cong ≈₁-refl (≈₁-sym bc=b) ⟩
        a • (b • c)        ≈⟨ ≈₁-sym (•-assoc a b c) ⟩
        (a • b) • c        ≈⟨ •-cong ab=a ≈₁-refl ⟩
        a • c              ≈⟨ ac=c ⟩
        c                  ∎
        where open EqReasoning S₁

      -- Note: commutativity is required
      ac=c->bc=c : (a • c) ≈₁ c → (b • c) ≈₁ c
      ac=c->bc=c ac=c = begin
        b • c              ≈⟨ •-cong ≈₁-refl (≈₁-sym (ac=c->a=c ac=c)) ⟩
        b • a              ≈⟨ •-comm b a ⟩
        a • b              ≈⟨ ab=a ⟩
        a                  ≈⟨ ac=c->a=c ac=c ⟩
        c                  ∎
        where open EqReasoning S₁

      ¬ac=c : (a • c) ≉₁ c
      ¬ac=c = ¬bc=c ∘ ac=c->bc=c

      prf : L₂ (a • b) c x z  ≈₂ L₂ a (b • c) x y
      prf = begin
        L₂ (a • b) c x z           ≈⟨ L₂-cong ab=a ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
        L₂ a c x z                 ≈⟨ Lex₂-case₁ ac=a ¬ac=c ⟩
        x                          ≈⟨ ≈₂-sym (Lex₂-case₁ ab=a ¬ab=b) ⟩
        L₂ a b x y                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
        L₂ a (b • c) x y           ∎
        where open EqReasoning S₂

    ... | yes ab=a | no ¬ab=b | no ¬bc=b | yes bc=c = prf
      where
      prf : L₂ (a • b) c x z  ≈₂ L₂ a (b • c) x z
      prf = begin
            L₂ (a • b) c x z           ≈⟨ L₂-cong ab=a ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
            L₂ a c x z                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=c) ≈₂-refl ≈₂-refl  ⟩
            L₂ a (b • c) x z           ∎
            where open EqReasoning S₂

    ... | no ¬ab=a | yes ab=b | yes bc=b | yes bc=c = prf
      where
      prf : L₂ (a • b) c y z  ≈₂ L₂ a (b • c) x (y ◦ z)
      prf = begin
            L₂ (a • b) c y z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl ⟩
            L₂ b c y z                 ≈⟨ Lex₂-case₃ bc=b bc=c ⟩
            y ◦ z                      ≈⟨ ≈₂-sym (Lex₂-case₂ ¬ab=a ab=b) ⟩
            L₂ a b x (y ◦ z)           ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x (y ◦ z)     ∎
            where open EqReasoning S₂

    ... | no ¬ab=a | yes ab=b | yes bc=b | no ¬bc=c = prf
      where
      prf : L₂ (a • b) c y z  ≈₂ L₂ a (b • c) x y
      prf = begin
            L₂ (a • b) c y z     ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl ⟩
            L₂ b c y z           ≈⟨ Lex₂-case₁ bc=b ¬bc=c ⟩
            y                    ≈⟨ ≈₂-sym (Lex₂-case₂ ¬ab=a ab=b) ⟩
            L₂ a b x y           ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x y     ∎
            where open EqReasoning S₂

    ... | no ¬ab=a | yes ab=b | no ¬bc=b | yes bc=c = prf
      where
      ac=c : (a • c) ≈₁ c
      ac=c = begin
             (a • c)            ≈⟨ •-cong ≈₁-refl (≈₁-sym bc=c) ⟩
             a • (b • c)        ≈⟨ ≈₁-sym (•-assoc a b c) ⟩
             (a • b) • c        ≈⟨ •-cong ab=b ≈₁-refl  ⟩
             b • c              ≈⟨ bc=c ⟩
             c                  ∎
             where open EqReasoning S₁

      ac=a->a=c : (a • c) ≈₁ a → a ≈₁ c
      ac=a->a=c ac=a = begin
             a                  ≈⟨ ≈₁-sym ac=a ⟩
             a • c              ≈⟨ •-cong ≈₁-refl (≈₁-sym bc=c) ⟩
             a • (b • c)        ≈⟨ ≈₁-sym (•-assoc a b c) ⟩
             (a • b) • c        ≈⟨ •-cong ab=b ≈₁-refl ⟩
             b • c              ≈⟨ bc=c ⟩
             c                  ∎
             where open EqReasoning S₁

      -- Note: commutativity is required
      ac=a->ab=a : (a • c) ≈₁ a → (a • b) ≈₁ a
      ac=a->ab=a ac=a = begin
             a • b              ≈⟨ •-cong (ac=a->a=c ac=a) ≈₁-refl ⟩
             c • b              ≈⟨ •-comm c b ⟩
             b • c              ≈⟨ bc=c ⟩
             c                  ≈⟨ ≈₁-sym (ac=a->a=c ac=a) ⟩
             a                  ∎
             where open EqReasoning S₁

      ¬ac=a : (a • c) ≉₁ a
      ¬ac=a = ¬ab=a ∘ ac=a->ab=a

      prf : L₂ (a • b) c y z  ≈₂ L₂ a (b • c) x z
      prf = begin
            L₂ (a • b) c y z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl ⟩
            L₂ b c y z                 ≈⟨ Lex₂-case₂ ¬bc=b bc=c ⟩
            z                          ≈⟨ ≈₂-sym (Lex₂-case₂ ¬ac=a ac=c ) ⟩
            L₂ a c x z                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=c) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x z     ∎
            where open EqReasoning S₂

    ... | _        | _         | no ¬bc=b | no ¬bc=c = contradiction₂ (•-sel b c) ¬bc=b ¬bc=c
    ... | no ¬ab=a | no ¬ab=b  | _        | _        = contradiction₂ (•-sel a b) ¬ab=a ¬ab=b

    L₂-comm : Commutative _≈₁_ _•_ → Commutative _≈₂_ _◦_ → ∀ a b x y → L₂ a b x y ≈₂ L₂ b a y x
    L₂-comm •-comm ◦-comm a b x y with (a • b) ≟₁ a | (a • b) ≟₁ b | (b • a) ≟₁ b | (b • a) ≟₁ a
    ... | yes p | yes p₁ | yes p₂ | yes p₃ = ◦-comm x y
    ... | yes p | yes p₁ | yes p₂ | no ¬p  = contradiction (≈₁-trans (•-comm b a) p) ¬p
    ... | yes p | yes p₁ | no ¬p  | yes p₂ = contradiction (≈₁-trans (•-comm b a) p₁) ¬p
    ... | yes p | yes p₁ | no ¬p  | no ¬p₁ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | yes p | no ¬p  | yes p₁ | yes p₂ = contradiction (≈₁-trans (•-comm a b) p₁) ¬p
    ... | yes p | no ¬p  | yes p₁ | no ¬p₁ = contradiction (≈₁-trans (•-comm a b) p₁) ¬p
    ... | yes p | no ¬p  | no ¬p₁ | yes p₁ = ≈₂-refl
    ... | yes p | no ¬p  | no ¬p₁ | no ¬p₂ = contradiction (≈₁-trans (•-comm b a) p) ¬p₂
    ... | no ¬p | yes p  | yes p₁ | yes p₂ = contradiction (≈₁-trans (•-comm a b) p₂) ¬p
    ... | no ¬p | yes p  | yes p₁ | no ¬p₁ = ≈₂-refl
    ... | no ¬p | yes p  | no ¬p₁ | yes p₁ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | no ¬p | yes p  | no ¬p₁ | no ¬p₂ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | no ¬p | no ¬p₁ | yes p  | yes p₁ = ◦-comm x y
    ... | no ¬p | no ¬p₁ | yes p  | no ¬p₂ = contradiction (≈₁-trans (•-comm a b) p) ¬p₁
    ... | no ¬p | no ¬p₁ | no ¬p₂ | yes p  = contradiction (≈₁-trans (•-comm a b) p) ¬p
    ... | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = ◦-comm x y

    --------------
    -- End private
    --------------

  cong : Congruent₂ _≈ₓ_ _⊕_
  cong (a≈b , w≈x) (c≈d , y≈z) =
    •-cong a≈b c≈d ,
    L₂-cong a≈b c≈d w≈x y≈z

  assoc : Associative _≈₁_ _•_ → Associative _≈₂_ _◦_ → Selective _≈₁_ _•_ → Commutative _≈₁_ _•_ → Associative _≈ₓ_ _⊕_
  assoc •-assoc ◦-assoc •-sel •-comm (a , x) (b , y) (c , z) =
    •-assoc a b c ,
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z

  comm : Commutative _≈₁_ _•_ → Commutative _≈₂_ _◦_ → Commutative _≈ₓ_ _⊕_
  comm •-comm ◦-comm (a , x) (b , y) =
    •-comm a b ,
    L₂-comm •-comm ◦-comm a b x y

  sel : Selective _≈₁_ _•_ → Selective _≈₂_ _◦_ → Selective _≈ₓ_ _⊕_
  sel •-sel ◦-sel (a , x) (b , y) with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | no  a•b≉a | no  a•b≉b  = contradiction₂ (•-sel a b) a•b≉a a•b≉b 
  ... | yes a•b≈a | no  _      = inj₁ (a•b≈a , ≈₂-refl)
  ... | no  _     | yes a•b≈b  = inj₂ (a•b≈b , ≈₂-refl)
  ... | yes a•b≈a | yes a•b≈b  = [ inj₁ ∘ (a•b≈a ,_) , inj₂ ∘ (a•b≈b ,_) ] (◦-sel x y)

  zeroʳ : ∀ {0₁ 0₂} → RightZero _≈₁_ 0₁ _•_ → RightZero _≈₂_ 0₂ _◦_ → RightZero _≈ₓ_ (0₁ , 0₂) _⊕_
  zeroʳ {0₁} {0₂} zeroʳ₁ zeroʳ₂ (x , a) with (x • 0₁) ≟₁ x | (x • 0₁) ≟₁ 0₁
  ... | _     | no  x•0≉0 = contradiction (zeroʳ₁ x) x•0≉0
  ... | no  _ | yes x•0≈0 = x•0≈0 , ≈₂-refl
  ... | yes _ | yes _     = zeroʳ₁ x , zeroʳ₂ a

  identityʳ : ∀ {0₁ 0₂} → RightIdentity _≈₁_ 0₁ _•_ → RightIdentity _≈₂_ 0₂ _◦_ → RightIdentity _≈ₓ_ (0₁ , 0₂) _⊕_
  identityʳ {0₁} {0₂} identityʳ₁ identityʳ₂ (x , a) with (x • 0₁) ≟₁ x | (x • 0₁) ≟₁ 0₁
  ... | no  x∙0≉x | _     = contradiction (identityʳ₁ x) x∙0≉x
  ... | yes x•0≈x | no  _ = x•0≈x , ≈₂-refl
  ... | yes _     | yes _ = identityʳ₁ x , identityʳ₂ a

  Lex-case-1 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≉₁ b → (a , x) ⊕ (b , y) ≈ₓ (a , x)
  Lex-case-1 {a} {b} x y ab=a ¬ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = contradiction p₁ ¬ab=b
  ... | yes p | no ¬p  = ab=a , ≈₂-refl
  ... | no ¬p | yes p  = contradiction ab=a ¬p
  ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

  Lex-case-2 : ∀ {a b} x y  → (a • b) ≉₁ a → (a • b) ≈₁ b → (a , x) ⊕ (b , y) ≈ₓ (b , y)
  Lex-case-2 {a} {b} x y ¬ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = contradiction p ¬ab=a
  ... | yes p | no ¬p  = contradiction p ¬ab=a
  ... | no ¬p | yes p  = ab=b , ≈₂-refl
  ... | no ¬p | no ¬p₁ = contradiction ab=b ¬p₁

  Lex-case-3 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≈₁ b → (a , x) ⊕ (b , y) ≈ₓ (a , x ◦ y)
  Lex-case-3 {a} {b} x y ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = ab=a , ≈₂-refl
  ... | yes p | no ¬p  = contradiction ab=b ¬p
  ... | no ¬p | yes p  = contradiction ab=a ¬p
  ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

