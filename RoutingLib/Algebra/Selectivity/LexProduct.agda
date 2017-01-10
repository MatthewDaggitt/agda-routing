
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; Decidable; IsDecEquivalence; Reflexive)
open import Relation.Binary.Product.Pointwise using (_×-Rel_)
open import Algebra.FunctionProperties.Core using (Op₂)
open import Algebra.FunctionProperties using (Commutative; Associative; Idempotent)

open import RoutingLib.Algebra.FunctionProperties using (Selective; _Preserves_)


module RoutingLib.Algebra.Selectivity.LexProduct 
  {a₁ a₂ ℓ₁} {A₁ : Set a₁} {A₂ : Set a₂} 
  (_≈₁_ : Rel A₁ ℓ₁) (≈₁-isDecEquivalence : IsDecEquivalence _≈₁_)
  (_•_ : Op₂ A₁) (•-sel : Selective _≈₁_ _•_)
  (_◦_ : Op₂ A₂)
  where

  open IsDecEquivalence ≈₁-isDecEquivalence
  open import RoutingLib.Algebra.Selectivity.Properties _≈₁_ _•_ •-sel

  select : ∀ x y → SelCase x y
  select = selection sym trans _≟_

  _⊕_ : Op₂ (A₁ × A₂)
  (a₁ , b₁) ⊕ (a₂ , b₂) with select a₁ a₂
  ... | sel₁ _ _ = (a₁ , b₁)
  ... | sel₂ _ _ = (a₂ , b₂)
  ... | sel≈ _ _ = (a₁ , b₁ ◦ b₂)
  
  ----------------
  -- Properties --
  ----------------

  module Properties {ℓ₂} (_≈₂_ : Rel A₂ ℓ₂) where

    comm : Commutative _≈₁_ _•_ → Reflexive _≈₂_ → Commutative _≈₂_ _◦_ → Commutative (_≈₁_ ×-Rel _≈₂_) _⊕_
    comm •-comm refl₂ ◦-comm (w , x) (y , z) with select w y | select y w
    ... | sel₁ _     w•y≉y | sel₁ y•w≈y _     = contradiction (trans (•-comm w y) y•w≈y) w•y≉y
    ... | sel₁ _     _     | sel₂ _     _     = refl , refl₂
    ... | sel₁ _     w•y≉y | sel≈ y•w≈y _     = contradiction (trans (•-comm w y) y•w≈y) w•y≉y
    ... | sel₂ _     _     | sel₁ _     _     = refl , refl₂
    ... | sel₂ _     w•y≈y | sel₂ y•w≉y _     = contradiction (trans (•-comm y w) w•y≈y) y•w≉y
    ... | sel₂ w•y≉w _     | sel≈ _     y•w≈w = contradiction (trans (•-comm w y) y•w≈w) w•y≉w
    ... | sel≈ w•y≈w _     | sel₁ _     y•w≉w = contradiction (trans (•-comm y w) w•y≈w) y•w≉w
    ... | sel≈ _     w•y≈y | sel₂ y•w≉y _     = contradiction (trans (•-comm y w) w•y≈y) y•w≉y
    ... | sel≈ _     _     | sel≈ y•w≈y y•w≈w = trans (sym y•w≈w) y•w≈y , ◦-comm x z


    sel : Reflexive _≈₂_ → Selective _≈₂_ _◦_ → Selective (_≈₁_ ×-Rel _≈₂_) _⊕_
    sel refl₂ ◦-sel (w , x) (y , z) with select w y
    ... | sel₁ _ _ = inj₁ (refl , refl₂)
    ... | sel₂ _ _ = inj₂ (refl , refl₂)
    ... | sel≈ w•y≈w w•y≈y with ◦-sel x z
    ...   | inj₁ x◦z=x = inj₁ (refl , x◦z=x)
    ...   | inj₂ x◦z=z = inj₂ (trans (sym w•y≈w) w•y≈y , x◦z=z)


    assoc : Commutative _≈₁_ _•_ → _•_ Preserves _≈₁_ → Associative _≈₁_ _•_ → Reflexive _≈₂_ → Associative _≈₂_ _◦_ → Associative (_≈₁_ ×-Rel _≈₂_) _⊕_
    assoc •-comm •-pres-≈₁ •-assoc refl₂ ◦-assoc  = associative
      where
      ≈-switch : ∀ {a b c} → (a • b) ≈₁ c → (b • a) ≈₁ c
      ≈-switch {a} {b} a•b≈c = trans (•-comm b a) a•b≈c

      ≉-switch : ∀ {a b c} → ¬ ((a • b) ≈₁ c) → ¬ ((b • a) ≈₁ c)
      ≉-switch {a} {b} a•b≉c b•a≈c = a•b≉c (≈-switch b•a≈c)

      -- Coincidently the proof of transitivity for the right natural order!
      lemma : ∀ {a} {b} {c} → (a • b) ≈₁ a → (b • c) ≈₁ b → (a • c) ≈₁ a
      lemma {a} {b} {c} a•b≈a b•c≈b =
        begin
          a • c
        ≈⟨ •-pres-≈₁ (sym a•b≈a) refl ⟩
          (a • b) • c
        ≈⟨ •-assoc a b c ⟩
          a • (b • c)
        ≈⟨ •-pres-≈₁ refl b•c≈b ⟩
          a • b
        ≈⟨ a•b≈a ⟩
          a
        ∎
        where open import Relation.Binary.EqReasoning (record {_≈_ = _≈₁_; isEquivalence = isEquivalence})

      associative : Associative (_≈₁_ ×-Rel _≈₂_) _⊕_
      associative (a , x) (b , y) (c , z) with select a b | select b c
      associative (a , x) (b , y) (c , z) | sel₁ a•b≈a a•b≉b | sel₁ b•c≈b b•c≉c with select a b | select a c 
      ... | sel₁ _     _     | sel₁ _     _     = refl , refl₂
      ... | sel₁ _     _     | sel₂ a•c≉a _     = contradiction (lemma a•b≈a b•c≈b) a•c≉a
      ... | sel₁ _     _     | sel≈ _     a•c≈c = contradiction (lemma (≈-switch a•c≈c) a•b≈a) (≉-switch b•c≉c)
      ... | sel₂ _     a•b≈b | _                = contradiction a•b≈b a•b≉b 
      ... | sel≈ _     a•b≈b | _                = contradiction a•b≈b a•b≉b 
      associative (a , x) (b , y) (c , z) | sel₁ _     _     | sel₂ _     _ = refl , refl₂
      associative (a , x) (b , y) (c , z) | sel₁ a•b≈a a•b≉b | sel≈ b•c≈b b•c≈c with select a b | select a c
      ... | sel₁ _     _     | sel₁ _     _     = refl , refl₂
      ... | sel₁ _     _     | sel₂ _     a•c≈c = contradiction (lemma b•c≈b (≈-switch a•c≈c)) (≉-switch a•b≉b)
      ... | sel₁ _     _     | sel≈ _     a•c≈c = contradiction (lemma b•c≈b (≈-switch a•c≈c)) (≉-switch a•b≉b) 
      ... | sel₂ _     a•b≈b | _                = contradiction a•b≈b a•b≉b
      ... | sel≈ _     a•b≈b | _                = contradiction a•b≈b a•b≉b 
      associative (a , x) (b , y) (c , z) | sel₂ a•b≉a a•b≈b | sel₁ b•c≈b b•c≉c with select a b | select b c
      ... | sel₁ a•b≈a _     | _                = contradiction a•b≈a a•b≉a
      ... | sel₂ _     _     | sel₁ _     _     = refl , refl₂
      ... | sel₂ _     _     | sel₂ a•c≉a _     = contradiction (lemma (•-idem b) b•c≈b) a•c≉a
      ... | sel₂ _     _     | sel≈ _     a•c≈c = contradiction (lemma (≈-switch a•c≈c) (•-idem b)) (≉-switch b•c≉c)
      ... | sel≈ a•b≈a _     | _                = contradiction a•b≈a a•b≉a 
      associative (a , x) (b , y) (c , z) | sel₂ a•b≉a a•b≈b | sel₂ b•c≉b b•c≈c with select a c | select b c
      ... | _                | sel₁ b•c≈b _     = contradiction b•c≈b b•c≉b
      ... | sel₁ a•c≈a _     | sel₂ _     _     = contradiction (lemma (≈-switch a•b≈b) a•c≈a) b•c≉b
      ... | sel₂ _     _     | sel₂ _     _     = refl , refl₂
      ... | sel≈ a•c≈a _     | sel₂ _     _     = contradiction (lemma a•c≈a (≈-switch b•c≈c)) a•b≉a
      ... | _                | sel≈ b•c≈b _     = contradiction b•c≈b b•c≉b
      associative (a , x) (b , y) (c , z) | sel₂ a•b≉a a•b≈b | sel≈ b•c≈b b•c≈c with select a b | select b c
      ... | sel₁ a•b≈a _     | _                = contradiction a•b≈a a•b≉a
      ... | sel₂ _     _     | sel₁ _     b•c≉c = contradiction b•c≈c b•c≉c
      ... | sel₂ _     _     | sel₂ b•c≉b _     = contradiction b•c≈b b•c≉b
      ... | sel₂ _     _     | sel≈ _     _     = refl , refl₂
      ... | sel≈ a•b≈a _     | _                = contradiction a•b≈a a•b≉a
      associative (a , x) (b , y) (c , z) | sel≈ a•b≈a a•b≈b | sel₁ b•c≈b b•c≉c with select a b | select a c
      ... | sel₁ _     a•b≉b | _                = contradiction a•b≈b a•b≉b
      ... | sel₂ a•b≉a _     | _                = contradiction a•b≈a a•b≉a
      ... | sel≈ _     _     | sel₁ _     _     = refl , refl₂
      ... | sel≈ _     _     | sel₂ a•c≉a _     = contradiction (lemma a•b≈a b•c≈b) a•c≉a
      ... | sel≈ _     _     | sel≈ _     a•c≈c = contradiction (lemma (≈-switch a•c≈c) a•b≈a) (≉-switch b•c≉c)
      associative (a , x) (b , y) (c , z) | sel≈ _     a•b≈b | sel₂ b•c≉b b•c≈c with select a c
      ... | sel₁ a•c≈a _     = contradiction (lemma (≈-switch a•b≈b) a•c≈a) b•c≉b
      ... | sel₂ _     _     = refl , refl₂
      ... | sel≈ a•c≈a _     = contradiction (lemma (≈-switch a•b≈b) a•c≈a) b•c≉b
      associative (a , x) (b , y) (c , z) | sel≈ a•b≈a a•b≈b | sel≈ b•c≈b b•c≈c with select a b | select a c
      ... | sel₁ _     a•b≉b | _                = contradiction a•b≈b a•b≉b
      ... | sel₂ a•b≉a _     | _                = contradiction a•b≈a a•b≉a
      ... | sel≈ _     _     | sel₁ _     a•c≉c = contradiction (lemma (≈-switch b•c≈c) (≈-switch a•b≈b)) (≉-switch a•c≉c)
      ... | sel≈ _     _     | sel₂ a•c≉a _     = contradiction (lemma a•b≈a b•c≈b) a•c≉a
      ... | sel≈ _     _     | sel≈ _     _     = refl , ◦-assoc x y z

    
    preserves : _•_ Preserves _≈₁_ → _◦_ Preserves _≈₂_ → _⊕_ Preserves (_≈₁_ ×-Rel _≈₂_)
    preserves •-pres ◦-pres {a , _} {b , _} {c , _} {d , _} (a≈b , w≈x) (c≈d , y≈z) with select a c | select b d
    ... | sel₁ a•c≈a a•c≉c | sel₁ b•d≈b b•d≉d = a≈b , w≈x
    ... | sel₁ a•c≈a a•c≉c | sel₂ b•d≉b b•d≈d = contradiction (trans (trans (sym (•-pres a≈b c≈d)) a•c≈a) a≈b) b•d≉b
    ... | sel₁ a•c≈a a•c≉c | sel≈ b•d≈b b•d≈d = contradiction (trans (trans (•-pres a≈b c≈d) b•d≈d) (sym c≈d)) a•c≉c
    ... | sel₂ a•c≉a a•c≈c | sel₁ b•d≈b b•d≉d = contradiction (trans (trans (•-pres a≈b c≈d) b•d≈b) (sym a≈b)) a•c≉a
    ... | sel₂ a•c≉a a•c≈c | sel₂ b•d≉b b•d≈d = c≈d , y≈z
    ... | sel₂ a•c≉a a•c≈c | sel≈ b•d≈b b•d≈d = contradiction (trans (trans (•-pres a≈b c≈d) b•d≈b) (sym a≈b)) a•c≉a
    ... | sel≈ a•c≈a a•c≈c | sel₁ b•d≈b b•d≉d = contradiction (trans (trans (sym (•-pres a≈b c≈d)) a•c≈c) c≈d) b•d≉d
    ... | sel≈ a•c≈a a•c≈c | sel₂ b•d≉b b•d≈d = contradiction (trans (trans (sym (•-pres a≈b c≈d)) a•c≈a) a≈b) b•d≉b
    ... | sel≈ a•c≈a a•c≈c | sel≈ b•d≈b b•d≈d = trans (trans (sym a•c≈a) (•-pres a≈b c≈d)) b•d≈b , ◦-pres w≈x y≈z

  open Properties public
