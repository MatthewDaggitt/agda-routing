open import Algebra using (Monoid)

module RoutingLib.db716.Data.List.Properties.MonoidFolds {c ℓ} (M : Monoid c ℓ) where
  open Monoid M renaming (Carrier to C)

  open import Data.List

  foldr' = foldr _∙_ ε
  
  foldr-++-commute : ∀ (xs ys : List C) → foldr' (xs ++ ys) ≈ foldr' xs ∙ foldr' ys
  foldr-++-commute [] ys = sym (identityˡ _)
  foldr-++-commute (x ∷ xs) ys = trans (∙-cong refl (foldr-++-commute xs ys)) (sym (assoc x (foldr' xs) (foldr' ys)))

  foldr-map : ∀ {a} {A : Set a} (xs : List A) (f : A → C) → foldr (λ x y → f x ∙ y) ε xs ≈ foldr' (map f xs)
  foldr-map [] f = refl
  foldr-map (x ∷ xs) f = ∙-cong refl (foldr-map xs f)
