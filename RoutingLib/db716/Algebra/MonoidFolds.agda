open import Algebra using (Monoid)
open import Data.Bool using (T)
--open import Data.List using (List; []; _∷_; foldr)
--open import Data.List.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Level using (Lift)
--open import Relation.Unary using (⊤)


module db716.Algebra.MonoidFolds {c ℓ} (Mon : Monoid c ℓ) where

open Monoid Mon renaming (Carrier to M)

{-record Foldable {a b} : Set (Level.suc (a Level.⊔ b)) where
  field
    t : Set a → Set a
    foldr : {A : Set a} {B : Set b} → (A → B → B) → B → t A → B-}

module _ (t : ∀ {a} → Set a → Set a) (foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → t A → B) where
  
  open import Relation.Binary.EqReasoning setoid

  all : ∀ {a} → (M → Set a) → t M → Set a
  all {a} P = foldr (λ m ts → (P m) × ts) (Lift a ⊤)

  head : ∀ {a} {A : Set a} → t A → Maybe A
  head = foldr (λ x y → just x) nothing

  {-
  cmp : ∀ {a} → (M → M → Set a) → t M → t M → Set a
  cmp {a} P xs ys = foldr f g xs
    where f x xs cont = cont x
          g = foldr (λ y ys → λ x xs → x ≈ y × xs rest ) (λ x → Lift a ⊤)  ys
  -}

  fold = foldr _∙_ ε

  -- Folding _∙_ over a list of identity elements yields the identity element
  fold[ids]≈id : {ms : t M} → all (_≈ ε) ms → fold ms ≈ ε
  fold[ids]≈id {ms} ms≈ε = {!!}

  {-fold[ids]≈id {[]} _ = refl
  fold[ids]≈id {m ∷ ms} (m≈ε , ms≈ε) = begin
    fold (m ∷ ms) ≡⟨⟩
    m ∙ fold ms ≈⟨ ∙-cong m≈ε refl ⟩
    ε ∙ fold ms ≈⟨ identityˡ (fold ms) ⟩
    fold ms ≈⟨  fold[ids]≈id {ms} ms≈ε  ⟩
    ε ∎-}
  
