open import Relation.Binary using (Setoid)
open import Data.Product using (_,_)

module RoutingLib.Algebra.FunctionProperties.Consequences {a ℓ} (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  open import Algebra.FunctionProperties _≈_
  open import Relation.Binary.EqReasoning S

  idˡ-subst : ∀ {_•_ e f} → Congruent₂ _•_ → LeftIdentity e _•_ → e ≈ f → LeftIdentity f _•_
  idˡ-subst {_•_} {e} {f} cong id e≈f x = begin
    f • x ≈⟨ cong (sym e≈f) refl ⟩
    e • x ≈⟨ id x ⟩
    x     ∎

  idʳ-subst : ∀ {_•_ e f} → Congruent₂ _•_ → RightIdentity e _•_ → e ≈ f → RightIdentity f _•_
  idʳ-subst {_•_} {e} {f} cong id e≈f x = begin
    x • f ≈⟨ cong refl (sym e≈f) ⟩
    x • e ≈⟨ id x ⟩
    x     ∎

  id-subst : ∀ {_•_ e f} → Congruent₂ _•_ → Identity e _•_ → e ≈ f → Identity f _•_
  id-subst cong (idˡ , idʳ) e≈f = idˡ-subst cong idˡ e≈f , idʳ-subst cong idʳ e≈f

  idˡ+zeˡ⇒singleton : ∀ {_•_ e} → LeftIdentity e _•_ → LeftZero e _•_ →
                     ∀ x y → x ≈ y
  idˡ+zeˡ⇒singleton {_•_} {e} id ze x y = begin
    x     ≈⟨ sym (id x) ⟩
    e • x ≈⟨ ze x ⟩
    e     ≈⟨ sym (ze y) ⟩
    e • y ≈⟨ id y ⟩
    y     ∎

  idʳ+zeʳ⇒singleton : ∀ {_•_ e} → RightIdentity e _•_ → RightZero e _•_ →
                      ∀ x y → x ≈ y
  idʳ+zeʳ⇒singleton {_•_} {e} id ze x y = begin
    x     ≈⟨ sym (id x) ⟩
    x • e ≈⟨ ze x ⟩
    e     ≈⟨ sym (ze y) ⟩
    y • e ≈⟨ id y ⟩
    y     ∎

  id+ze⇒singleton : ∀ {_•_ e} → Identity e _•_ → Zero e _•_ → ∀ x y → x ≈ y
  id+ze⇒singleton {_•_} (id , _) (ze , _) = idˡ+zeˡ⇒singleton {_•_} id ze
