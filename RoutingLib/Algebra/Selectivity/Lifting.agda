
open import Algebra.FunctionProperties using (Op₂; Associative; Idempotent; Commutative)
open import Relation.Binary using (Rel; Reflexive; Decidable; Transitive; Symmetric; IsEquivalence)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_)
open import Level using (_⊔_)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (id; _on_)

open import RoutingLib.Algebra.FunctionProperties using (Selective; _Preserves_)

module RoutingLib.Algebra.Selectivity.Lifting 
  {a b ℓ} {A : Set a} (_≈_ : Rel A ℓ)
  (_•_ : Op₂ A) (•-sel : Selective _≈_ _•_)
  {B : Set b} (f : B → A) 
  where

  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _•_ •-sel using (•-idem)

  infix 7 _◦_
  _◦_ : Op₂ B
  x ◦ y with •-sel (f x) (f y)
  ... | inj₁ _ = x
  ... | inj₂ _ = y

  preserves : Symmetric _≈_ → Transitive _≈_ → _•_ Preserves _≈_ → _◦_ Preserves (_≈_ on f) 
  preserves sym trans resp {x = x} {y} {u} {v} fx≈fy fu≈fv with •-sel (f x) (f u) | •-sel (f y) (f v)
  ... | inj₁ fx•fu≈fx | inj₁ fy•fv≈fy = fx≈fy
  ... | inj₁ fx•fu≈fx | inj₂ fy•fv≈fv = trans (trans (sym fx•fu≈fx) (resp fx≈fy fu≈fv)) fy•fv≈fv
  ... | inj₂ fx•fu≈fu | inj₁ fy•fv≈fy = trans (trans (sym fx•fu≈fu) (resp fx≈fy fu≈fv)) fy•fv≈fy
  ... | inj₂ fx•fu≈fu | inj₂ fy•fv≈fv = fu≈fv

  distr : ∀ x y → (f x • f y) ≈ f (x ◦ y)
  distr x y with •-sel (f x) (f y)
  ... | inj₁ fx•fy≈fx = fx•fy≈fx
  ... | inj₂ fx•fy≈fy = fx•fy≈fy
  
  module Properties (_≈′_ : Rel B ℓ) (f-inj : ∀ {x y} → f x ≈ f y → x ≈′ y) where

    app : Symmetric _≈_ → Transitive _≈_ →  ∀ {x y} z → (f x • f y) ≈ f z → (x ◦ y) ≈′ z
    app sym trans {x} {y} z fx•fy≈fz with •-sel (f x) (f y)
    ... | inj₁ fx•fy≈fx = f-inj (trans (sym fx•fy≈fx) fx•fy≈fz)
    ... | inj₂ fx•fy≈fy = f-inj (trans (sym fx•fy≈fy) fx•fy≈fz)
      
    sel : Reflexive _≈_ → Selective _≈′_ _◦_
    sel refl x y with •-sel (f x) (f y)
    ... | inj₁ _ = inj₁ (f-inj refl)
    ... | inj₂ _ = inj₂ (f-inj refl)

    comm : Reflexive _≈_ → Symmetric _≈_ → Transitive _≈_ → Commutative _≈_ _•_ → Commutative _≈′_ _◦_
    comm refl sym trans comm x y with •-sel (f x) (f y) | •-sel (f y) (f x)
    ... | inj₁ x•y≈x | inj₁ y•x≈y = f-inj (trans (trans (sym x•y≈x) (comm (f x) (f y))) y•x≈y)
    ... | inj₁ _     | inj₂ _     = f-inj refl
    ... | inj₂ _     | inj₁ _     = f-inj refl
    ... | inj₂ x•y≈y | inj₂ y•x≈x = f-inj (trans (trans (sym x•y≈y) (comm (f x) (f y))) y•x≈x)

    assoc : Reflexive _≈_ → Symmetric _≈_ → Transitive _≈_ → _•_ Preserves _≈_ → Associative _≈_ _•_ → Associative _≈′_ _◦_
    assoc refl sym trans •-resp-≈ assoc = as
      where

      open import Relation.Binary.EqReasoning (record { Carrier = A ; _≈_ = _≈_ ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans } })

      lemma2 : ∀ {x y z} → (y • x) ≈ y → (z • y) ≈ z → (z • x) ≈ x → x ≈ z
      lemma2 {x} {y} {z} y•x≈y z•y≈z z•x≈x = (
        begin
          x
        ≈⟨ sym z•x≈x ⟩
          z • x
        ≈⟨ sym (•-resp-≈ z•y≈z refl) ⟩
          (z • y) • x
        ≈⟨ assoc z y x ⟩
          z • (y • x)
        ≈⟨ •-resp-≈ refl y•x≈y ⟩
          z • y
        ≈⟨ z•y≈z ⟩
          z
        ∎)
      
      as : Associative _≈′_ _◦_
      as x y z with •-sel (f x) (f y) | •-sel (f y) (f z)
      as x y z | inj₁ x•y≈x | inj₁ y•z≈y with •-sel (f x) (f y) | •-sel (f x) (f z)
      ... | inj₁ _     | inj₁ _     = f-inj refl
      ... | inj₁ _     | inj₂ x•z≈z = f-inj (lemma2 y•z≈y x•y≈x x•z≈z)
      ... | inj₂ x•y≈y | inj₁ _     = f-inj (trans (sym x•y≈x) x•y≈y)
      ... | inj₂ x•y≈y | inj₂ x•z≈z = f-inj (lemma2 (•-idem (f z)) y•z≈y (trans (•-resp-≈ (trans (sym x•y≈y) x•y≈x) (sym refl)) x•z≈z))
      as x y z | inj₁ _ | inj₂ _ with •-sel (f x) (f z)
      ... | inj₁ _ = (f-inj refl)
      ... | inj₂ _ = (f-inj refl)
      as x y z | inj₂ x•y≈y | inj₁ y•z≈y with •-sel (f x) (f y) | •-sel (f y) (f z)
      ... | inj₁ x•y≈x | inj₁ _     = f-inj (trans (sym x•y≈y) x•y≈x)
      ... | inj₁ x•y≈x | inj₂ y•z≈z = f-inj (trans (sym (trans (trans x•y≈y (sym y•z≈y)) y•z≈z)) x•y≈x)
      ... | inj₂ _     | inj₁ _     = f-inj refl
      ... | inj₂ _     | inj₂ y•z≈z = f-inj (trans (sym y•z≈z) y•z≈y)
      as x y z | inj₂ x•y≈y | inj₂ y•z≈z with •-sel (f x) (f z) | •-sel (f y) (f z)
      ... | inj₁ x•z≈x | inj₁ y•z≈y     = f-inj (lemma2 (trans (trans (sym (•-resp-≈ y•z≈z y•z≈y)) (•-resp-≈ y•z≈y y•z≈z)) y•z≈z) x•z≈x x•y≈y)
      ... | inj₁ x•z≈x | inj₂ _     = f-inj (
        begin
          f z
        ≈⟨ sym y•z≈z ⟩
          f y • f z
        ≈⟨ •-resp-≈ (sym x•y≈y) refl ⟩
          (f x • f y) • f z
        ≈⟨ assoc (f x) (f y) (f z) ⟩
          f x • (f y • f z)
        ≈⟨ •-resp-≈ refl y•z≈z ⟩
          f x • f z
        ≈⟨ x•z≈x ⟩
          f x
        ∎)
      ... | inj₂ _     | inj₁ y•z≈y = f-inj (trans (sym y•z≈y) y•z≈z)
      ... | inj₂ _     | inj₂ _     = (f-inj refl)

  open Properties public
