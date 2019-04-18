

module RoutingLib.Algebra.Construct.Lexicographic where

open import Algebra.FunctionProperties
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Function
open import RoutingLib.Algebra.FunctionProperties

module _ {a b ℓ} {A : Set a} {B : Set b} {_≈_ : Rel A ℓ}
         (_≟_ : Decidable _≈_) (_•_ : Op₂ A) (_◦_ : Op₂ B) where

  -- Note: for non-selective • the result in the no+no case must be
  -- the identity of B (for associativity to hold).
  Lex₂ : A  → A  → B  → B → B
  Lex₂ a b x y with (a • b) ≟ a | (a • b) ≟ b
  ... | yes _ | no  _ = x
  ... | no  _ | yes _ = y
  ... |     _ |     _ = x ◦ y

  Lex : Op₂ (A × B)
  Lex (a , x) (b , y) = (a • b , Lex₂ a b x y)


module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel B ℓ₂}
         (≈₁-isDecEquivalence : IsDecEquivalence _≈₁_)
         (≈₂-isEquivalence : IsEquivalence _≈₂_)
         (_•_ : Op₂ A) (_◦_ : Op₂ B)
         (•-cong : Congruent₂ _≈₁_ _•_) (◦-cong : Congruent₂ _≈₂_ _◦_) where

  private
    open IsDecEquivalence ≈₁-isDecEquivalence public
      using () renaming
      ( refl          to ≈₁-refl
      ; sym           to ≈₁-sym
      ; trans         to ≈₁-trans
      ; isEquivalence to ≈₁-isEquivalence
      ; _≟_           to _≟₁_
      )

    open IsEquivalence ≈₂-isEquivalence public
      using () renaming
      ( refl          to ≈₂-refl
      ; sym           to ≈₂-sym
      ; trans         to ≈₂-trans
      )

    infix 4 _≈ₓ_
    infix 7 _⊕_

    _≉₁_ : Rel A _
    x ≉₁ y = ¬ (x ≈₁ y)

    _⊕_ : Op₂ (A × B)
    _⊕_ = Lex _≟₁_ _•_ _◦_

    L₂ : A  → A  → B  → B → B
    L₂ = Lex₂ _≟₁_ _•_ _◦_

    _≈ₓ_ : Rel (A × B) (ℓ₁ ⊔ ℓ₂)
    _≈ₓ_ = Pointwise _≈₁_ _≈₂_

    ≈ₓ-isEquivalence : IsEquivalence _≈ₓ_
    ≈ₓ-isEquivalence = ×-isEquivalence ≈₁-isEquivalence ≈₂-isEquivalence

    open IsEquivalence  ≈ₓ-isEquivalence public
      using () renaming
      ( refl          to ≈ₓ-refl
      ; sym           to ≈ₓ-sym
      ; trans         to ≈ₓ-trans
      )

    S₁ : Setoid _ _
    S₁ = record { isEquivalence = ≈₁-isEquivalence }

    S₂ : Setoid _ _
    S₂ = record { isEquivalence = ≈₂-isEquivalence }

    Sₓ : Setoid _ _
    Sₓ = record { isEquivalence = ≈ₓ-isEquivalence }

    L₂-cong : ∀ {a₁ a₂ b₁ b₂ x₁ x₂ y₁ y₂}  → a₁ ≈₁ a₂ → b₁ ≈₁ b₂ → x₁ ≈₂ x₂ → y₁ ≈₂ y₂ → L₂ a₁ b₁ x₁ y₁ ≈₂ L₂ a₂ b₂ x₂ y₂
    L₂-cong  {a₁} {a₂} {b₁} {b₂} {x₁} {x₂} {y₁} {y₂} a₁≈a₂ b₁≈b₂ x₁≈x₂ y₁≈y₂ with (a₁ • b₁) ≟₁ a₁ | (a₁ • b₁) ≟₁ b₁ | (a₂ • b₂) ≟₁ a₂ | (a₂ • b₂) ≟₁ b₂
    ... | yes p | yes p₁ | yes p₂ | yes p₃ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | yes p | yes p₁ | no ¬p  | no ¬p₁ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | no ¬p | no ¬p₁ | yes p  | yes p₁ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = ◦-cong x₁≈x₂ y₁≈y₂
    ... | yes p | no ¬p  | yes p₁ | no ¬p₁ = x₁≈x₂
    ... | no ¬p | yes p  | no ¬p₁ | yes p₁ = y₁≈y₂
    ... | _     | yes p₁ | _      | no ¬p  = contradiction (≈₁-trans (≈₁-trans (•-cong (≈₁-sym a₁≈a₂) (≈₁-sym  b₁≈b₂)) p₁) b₁≈b₂) ¬p
    ... | yes p | _      | no ¬p  | _      = contradiction (≈₁-trans (≈₁-trans (•-cong (≈₁-sym a₁≈a₂) (≈₁-sym  b₁≈b₂)) p) a₁≈a₂) ¬p
    ... | _     | no ¬p  | _      | yes p₂ = contradiction (≈₁-trans (≈₁-trans (•-cong a₁≈a₂ b₁≈b₂ ) p₂) (≈₁-sym b₁≈b₂)) ¬p
    ... | no ¬p | _      | yes p  | _      = contradiction (≈₁-trans (≈₁-trans (•-cong a₁≈a₂ b₁≈b₂ ) p) (≈₁-sym a₁≈a₂)) ¬p

    Lex₂-case-1 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≉₁ b → L₂ a b x y ≈₂ x
    Lex₂-case-1 {a} {b} x y ab=a ¬ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = contradiction p₁ ¬ab=b
    ... | yes p | no ¬p = ≈₂-refl
    ... | no ¬p | yes p = contradiction ab=a ¬p
    ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

    Lex₂-case-2 : ∀ {a b} x y  → (a • b) ≉₁ a → (a • b) ≈₁ b → L₂ a b x y ≈₂ y
    Lex₂-case-2 {a} {b} x y ¬ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = contradiction p ¬ab=a
    ... | yes p | no ¬p = contradiction p ¬ab=a
    ... | no ¬p | yes p = ≈₂-refl
    ... | no ¬p | no ¬p₁ = contradiction ab=b ¬p₁

    Lex₂-case-3 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≈₁ b → L₂ a b x y ≈₂ (x ◦ y)
    Lex₂-case-3 {a} {b} x y ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
    ... | yes p | yes p₁ = ≈₂-refl
    ... | yes p | no ¬p = contradiction ab=b ¬p
    ... | no ¬p | yes p = contradiction ab=a ¬p
    ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

    L₂-assoc : Associative _≈₁_ _•_ → Associative _≈₂_ _◦_ → Selective _≈₁_ _•_ → Commutative _≈₁_ _•_ →
               ∀ a b c x y z  → L₂ (a • b) c (L₂ a b x y) z  ≈₂ L₂ a (b • c) x (L₂ b c y z)
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z with (a • b) ≟₁ a | (a • b) ≟₁ b | (b • c) ≟₁ b | (b • c) ≟₁ c
    ... | yes ab=a | yes ab=b | yes bc=b | yes bc=c = prf
      where
      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x (y ◦ z)
      prf = begin
            L₂ (a • b) c (x ◦ y) z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
            L₂ b c (x ◦ y) z                 ≈⟨ Lex₂-case-3 _ _ bc=b bc=c  ⟩
            (x ◦ y) ◦ z                      ≈⟨ ◦-assoc x y z ⟩
            x ◦ (y ◦ z)                      ≈⟨ ≈₂-sym (Lex₂-case-3 _ _ ab=a ab=b) ⟩
            L₂ a b x (y ◦ z)                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl   ⟩
            L₂ a (b • c) x (y ◦ z)     ∎
            where open EqReasoning S₂

    ... | yes ab=a | yes ab=b | yes bc=b | no ¬bc=c = prf
      where
      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x y
      prf = begin
            L₂ (a • b) c (x ◦ y) z           ≈⟨  L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
            L₂ b c (x ◦ y) z                 ≈⟨ Lex₂-case-1 _ _ bc=b ¬bc=c ⟩
            x ◦ y                            ≈⟨ ≈₂-sym (Lex₂-case-3 _ _ ab=a ab=b) ⟩
            L₂ a b x y                       ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl  ⟩
            L₂ a (b • c) x y     ∎
            where open EqReasoning S₂

    ... | yes ab=a | yes ab=b | no ¬bc=b | yes bc=c = prf
      where
      b=a : b ≈₁ a
      b=a = ≈₁-trans (≈₁-sym ab=b) ab=a

      prf : L₂ (a • b) c (x ◦ y) z  ≈₂ L₂ a (b • c) x z
      prf = begin
            L₂ (a • b) c (x ◦ y) z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
            L₂ b c (x ◦ y) z                 ≈⟨ Lex₂-case-2 _ _ ¬bc=b bc=c ⟩
            z                                ≈⟨ ≈₂-sym (Lex₂-case-2 _ _ ¬bc=b bc=c) ⟩
            L₂ b c x z                       ≈⟨ L₂-cong b=a (≈₁-sym bc=c) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x z     ∎
            where open EqReasoning S₂

    ... | yes ab=a | no ¬ab=b | yes bc=b | yes bc=c = prf
      where
      c=b : c ≈₁ b
      c=b = ≈₁-trans (≈₁-sym bc=c) bc=b

      prf : L₂ (a • b) c x z  ≈₂ L₂ a (b • c) x (y ◦ z)
      prf = begin
            L₂ (a • b) c x z           ≈⟨  L₂-cong ab=a c=b ≈₂-refl ≈₂-refl  ⟩
            L₂ a b x z                 ≈⟨ Lex₂-case-1 _ _ ab=a ¬ab=b ⟩
            x                          ≈⟨ ≈₂-sym (Lex₂-case-1 _ _ ab=a ¬ab=b) ⟩
            L₂ a b x (y ◦ z)          ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
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
      ¬ac=c = λ ac=c → ¬bc=c (ac=c->bc=c ac=c)

      prf : L₂ (a • b) c x z  ≈₂ L₂ a (b • c) x y
      prf = begin
          L₂ (a • b) c x z           ≈⟨ L₂-cong ab=a ≈₁-refl ≈₂-refl ≈₂-refl  ⟩
          L₂ a c x z                 ≈⟨ Lex₂-case-1 _ _ ac=a ¬ac=c ⟩
          x                          ≈⟨ ≈₂-sym (Lex₂-case-1 _ _ ab=a ¬ab=b) ⟩
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
            L₂ b c y z                 ≈⟨ Lex₂-case-3 _ _ bc=b bc=c ⟩
            y ◦ z                     ≈⟨ ≈₂-sym ( Lex₂-case-2 _ _  ¬ab=a ab=b) ⟩
            L₂ a b x (y ◦ z)          ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x (y ◦ z)     ∎
            where open EqReasoning S₂

    ... | no ¬ab=a | yes ab=b | yes bc=b | no ¬bc=c = prf
      where
      prf : L₂ (a • b) c y z  ≈₂ L₂ a (b • c) x y
      prf = begin
            L₂ (a • b) c y z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl ⟩
            L₂ b c y z                 ≈⟨ Lex₂-case-1 _ _ bc=b ¬bc=c ⟩
            y                          ≈⟨ ≈₂-sym (Lex₂-case-2 _ _ ¬ab=a ab=b) ⟩
            L₂ a b x y                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=b) ≈₂-refl ≈₂-refl ⟩
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
      ¬ac=a = λ ac=a → ¬ab=a (ac=a->ab=a ac=a)

      prf : L₂ (a • b) c y z  ≈₂ L₂ a (b • c) x z
      prf = begin
            L₂ (a • b) c y z           ≈⟨ L₂-cong ab=b ≈₁-refl ≈₂-refl ≈₂-refl ⟩
            L₂ b c y z                 ≈⟨ Lex₂-case-2 _ _ ¬bc=b bc=c ⟩
            z                          ≈⟨ ≈₂-sym (Lex₂-case-2 _ _ ¬ac=a ac=c ) ⟩
            L₂ a c x z                 ≈⟨ L₂-cong ≈₁-refl (≈₁-sym bc=c) ≈₂-refl ≈₂-refl ⟩
            L₂ a (b • c) x z     ∎
            where open EqReasoning S₂

    ... | _        | _         | no ¬bc=b | no ¬bc=c with •-sel b c
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z | _ | _ | no ¬bc=b | no ¬bc=c | _⊎_.inj₁ x₁ = contradiction x₁ ¬bc=b
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z | _ | _ | no ¬bc=b | no ¬bc=c | _⊎_.inj₂ y₁ = contradiction y₁ ¬bc=c

    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z | no ¬ab=a | no ¬ab=b  | _        | _   with •-sel a b
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z | no ¬ab=a | no ¬ab=b | _ | _ | _⊎_.inj₁ x₁ = contradiction x₁ ¬ab=a
    L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z | no ¬ab=a | no ¬ab=b | _ | _ | _⊎_.inj₂ y₁ = contradiction y₁ ¬ab=b

    L₂-comm : Commutative _≈₁_ _•_ → Commutative _≈₂_ _◦_ → ∀ a b x y → L₂ a b x y ≈₂ L₂ b a y x
    L₂-comm •-comm ◦-comm a b x y with (a • b) ≟₁ a | (a • b) ≟₁ b | (b • a) ≟₁ b | (b • a) ≟₁ a
    ... | yes p | yes p₁ | yes p₂ | yes p₃ = ◦-comm x y
    ... | yes p | yes p₁ | yes p₂ | no ¬p = contradiction (≈₁-trans (•-comm b a) p) ¬p
    ... | yes p | yes p₁ | no ¬p | yes p₂ = contradiction (≈₁-trans (•-comm b a) p₁) ¬p
    ... | yes p | yes p₁ | no ¬p | no ¬p₁ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | yes p | no ¬p | yes p₁ | yes p₂ = contradiction (≈₁-trans (•-comm a b) p₁) ¬p
    ... | yes p | no ¬p | yes p₁ | no ¬p₁ = contradiction (≈₁-trans (•-comm a b) p₁) ¬p
    ... | yes p | no ¬p | no ¬p₁ | yes p₁ = ≈₂-refl
    ... | yes p | no ¬p | no ¬p₁ | no ¬p₂ = contradiction (≈₁-trans (•-comm b a) p) ¬p₂
    ... | no ¬p | yes p | yes p₁ | yes p₂ = contradiction (≈₁-trans (•-comm a b) p₂) ¬p
    ... | no ¬p | yes p | yes p₁ | no ¬p₁ = ≈₂-refl
    ... | no ¬p | yes p | no ¬p₁ | yes p₁ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | no ¬p | yes p | no ¬p₁ | no ¬p₂ = contradiction (≈₁-trans (•-comm b a) p) ¬p₁
    ... | no ¬p | no ¬p₁ | yes p | yes p₁ = ◦-comm x y
    ... | no ¬p | no ¬p₁ | yes p | no ¬p₂ = contradiction (≈₁-trans (•-comm a b) p) ¬p₁
    ... | no ¬p | no ¬p₁ | no ¬p₂ | yes p = contradiction (≈₁-trans (•-comm a b) p) ¬p
    ... | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = ◦-comm x y

    --------------
    -- End private
    --------------

  cong : Congruent₂ _≈ₓ_ _⊕_
  cong {a , w} {b , x} {c , y} {d , z} (a≈b , w≈x) (c≈d , y≈z) = prf
    where
    prf : (a , w) ⊕ (c , y) ≈ₓ (b , x) ⊕ (d , z)
    prf = begin
          (a , w) ⊕ (c , y)             ≈⟨ ≈ₓ-refl ⟩
          (a • c ,  L₂ a c w y)         ≈⟨ (•-cong a≈b c≈d) , L₂-cong a≈b c≈d w≈x y≈z ⟩
          (b • d ,  L₂ b d x z)         ≈⟨ ≈ₓ-refl ⟩
          (b , x) ⊕ (d , z)                ∎
          where open EqReasoning Sₓ

  assoc : Associative _≈₁_ _•_ → Associative _≈₂_ _◦_ → Selective _≈₁_ _•_ → Commutative _≈₁_ _•_ → Associative _≈ₓ_ _⊕_
  assoc •-assoc ◦-assoc •-sel •-comm (a , x) (b , y) (c , z) = proof
    where
    proof : ((a , x) ⊕ (b , y)) ⊕ (c , z) ≈ₓ (a , x) ⊕ ((b , y) ⊕ (c , z))
    proof = begin
           ((a , x) ⊕ (b , y)) ⊕ (c , z)                ≈⟨ cong ≈ₓ-refl ≈ₓ-refl ⟩
           (a • b , L₂ a b x y) ⊕ (c , z)               ≈⟨ ≈ₓ-refl ⟩
           ((a • b) • c , L₂ (a • b) c (L₂ a b x y) z)  ≈⟨ •-assoc a b c , ≈₂-refl ⟩
           (a • (b • c) , L₂ (a • b) c (L₂ a b x y) z)  ≈⟨ ≈₁-refl , L₂-assoc •-assoc ◦-assoc •-sel •-comm a b c x y z ⟩
           (a • (b • c) , L₂ a (b • c) x (L₂ b c y z))  ≈⟨ cong ≈ₓ-refl ≈ₓ-refl ⟩
           (a , x) ⊕ (b • c , L₂ b c y z)               ≈⟨ cong ≈ₓ-refl ≈ₓ-refl ⟩
           (a , x) ⊕ ((b , y) ⊕ (c , z))    ∎
           where open EqReasoning Sₓ

  comm : Commutative _≈₁_ _•_ → Commutative _≈₂_ _◦_ → Commutative _≈ₓ_ _⊕_
  comm •-comm ◦-comm (a , x) (b , y) = proof
    where
    proof : (a , x) ⊕ (b , y) ≈ₓ (b , y) ⊕ (a , x)
    proof = begin
            (a , x) ⊕ (b , y)               ≈⟨ ≈ₓ-refl  ⟩
            (a • b , L₂ a b x y)            ≈⟨ •-comm a b  , L₂-comm •-comm ◦-comm  a b x y  ⟩
            (b • a , L₂ b a y x)            ≈⟨ ≈ₓ-refl  ⟩
            (b , y) ⊕ (a , x)    ∎
           where open EqReasoning Sₓ

  sel : Selective _≈₁_ _•_ → Selective _≈₂_ _◦_ → Selective _≈ₓ_ _⊕_
  sel •-sel ◦-sel (a , x) (b , y) with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes a•b≈a | no  _      = inj₁ (a•b≈a , ≈₂-refl)
  ... | no  _     | yes a•b≈b  = inj₂ (a•b≈b , ≈₂-refl)
  ... | yes a•b≈a | yes a•b≈b  with ◦-sel x y
  ...   | inj₁ x◦y≈x = inj₁ (a•b≈a , x◦y≈x)
  ...   | inj₂ x◦y≈y = inj₂ (a•b≈b , x◦y≈y)
  sel •-sel ◦-sel (a , x) (b , y) | no  a•b≉a | no  a•b≉b  with •-sel a b
  ...   | inj₁ a•b≈a = contradiction a•b≈a a•b≉a
  ...   | inj₂ a•b≈b = contradiction a•b≈b a•b≉b

  zeroʳ : ∀ {0₁ 0₂} → RightZero _≈₁_ 0₁ _•_ → RightZero _≈₂_ 0₂ _◦_ → RightZero _≈ₓ_ (0₁ , 0₂) _⊕_
  zeroʳ {0₁} {0₂} zeroʳ₁ zeroʳ₂ (x , a) with (x • 0₁) ≟₁ x | (x • 0₁) ≟₁ 0₁
  ... | _     | no x•0≉0 = contradiction (zeroʳ₁ x) x•0≉0
  ... | no  _ | yes x•0≈0    = x•0≈0 , ≈₂-refl
  ... | yes _ | yes _    = (zeroʳ₁ x) , (zeroʳ₂ a)

  identityʳ : ∀ {0₁ 0₂} → RightIdentity _≈₁_ 0₁ _•_ → RightIdentity _≈₂_ 0₂ _◦_ → RightIdentity _≈ₓ_ (0₁ , 0₂) _⊕_
  identityʳ {0₁} {0₂} identityʳ₁ identityʳ₂ (x , a) with (x • 0₁) ≟₁ x | (x • 0₁) ≟₁ 0₁
  ... | no  x∙0≉x | _     = contradiction (identityʳ₁ x) x∙0≉x
  ... | yes x•0≈x | no  _ = x•0≈x , ≈₂-refl
  ... | yes _     | yes _ = identityʳ₁ x , identityʳ₂ a

  Lex-case-1 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≉₁ b → (a , x) ⊕ (b , y) ≈ₓ (a , x)
  Lex-case-1 {a} {b} x y ab=a ¬ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = contradiction p₁ ¬ab=b
  ... | yes p | no ¬p = ab=a , ≈₂-refl
  ... | no ¬p | yes p = contradiction ab=a ¬p
  ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

  Lex-case-2 : ∀ {a b} x y  → (a • b) ≉₁ a → (a • b) ≈₁ b → (a , x) ⊕ (b , y) ≈ₓ (b , y)
  Lex-case-2 {a} {b} x y ¬ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = contradiction p ¬ab=a
  ... | yes p | no ¬p = contradiction p ¬ab=a
  ... | no ¬p | yes p = ab=b , ≈₂-refl
  ... | no ¬p | no ¬p₁ = contradiction ab=b ¬p₁

  Lex-case-3 : ∀ {a b} x y  → (a • b) ≈₁ a → (a • b) ≈₁ b → (a , x) ⊕ (b , y) ≈ₓ (a , x ◦ y)
  Lex-case-3 {a} {b} x y ab=a ab=b with (a • b) ≟₁ a | (a • b) ≟₁ b
  ... | yes p | yes p₁ = ab=a , ≈₂-refl
  ... | yes p | no ¬p = contradiction ab=b ¬p
  ... | no ¬p | yes p = contradiction ab=a ¬p
  ... | no ¬p | no ¬p₁ = contradiction ab=a ¬p

