open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (⊔-sel; m≤m⊔n)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map)
open import Data.List.Any as Any using (here; there)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (setoid; refl; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (tabulate; allFin; applyUpTo; applyDownFrom; upTo; downFrom; combine; max)
open import RoutingLib.Data.Nat.Properties using (≤+≢⇒<; 0-idᵣ-⊔; n≤m⊔n; ≤-trans)

module RoutingLib.Data.List.Any.PropositionalMembership where

  open Any.Membership-≡ public

  import RoutingLib.Data.List.Any.GenericMembership as GM

  ∈-map : ∀ {a b} {A : Set a} {B : Set b} {v xs}
          (f : A → B) → v ∈ xs → f v ∈ map f xs
  ∈-map {A = A} {B} f = GM.∈-map (setoid B) (setoid A) (cong f)

  ∈-combine : ∀ {a b} {A : Set a} {B : Set b} {u v xs ys}
              (f : A → A → B) → u ∈ xs → v ∈ ys → f u v ∈ combine f xs ys
  ∈-combine {A = A} {B} f = GM.∈-combine (setoid B) (setoid A) (cong₂ f)



  ∈-applyUpTo : ∀ {a} {A : Set a} (f : ℕ → A) {n i} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo f {_} {zero}  (s≤s _)   = here refl
  ∈-applyUpTo f {_} {suc i} (s≤s i<n) = there (∈-applyUpTo (f ∘ suc) i<n)

  ∈-applyDownFrom : ∀ {a} {A : Set a} (f : ℕ → A) {n i} → i < n → f i ∈ applyDownFrom f n
  ∈-applyDownFrom f {suc n} {i} (s≤s i≤n) with i ≟ n
  ... | yes i≡n = here (cong f i≡n)
  ... | no  i≢n = there (∈-applyDownFrom f (≤+≢⇒< i≤n i≢n))

  ∈-upTo : ∀ {n i} → i < n → i ∈ upTo n
  ∈-upTo i<n = ∈-applyUpTo id i<n

  ∈-downFrom : ∀ {n i} → i < n → i ∈ downFrom n
  ∈-downFrom i<n = ∈-applyDownFrom id i<n

  ∈-tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) i → f i ∈ tabulate f
  ∈-tabulate f fzero    = here refl
  ∈-tabulate f (fsuc i) = there (∈-tabulate (f ∘ fsuc) i)

  ∈-allFin : ∀ {n} i → i ∈ allFin n
  ∈-allFin = ∈-tabulate id

  max∈xs : ∀ {x xs} → max (x ∷ xs) ∈ x ∷ xs
  max∈xs {x} {[]} = here (0-idᵣ-⊔ x)
  max∈xs {x} {y ∷ xs} with ⊔-sel x (max (y ∷ xs))
  ... | inj₁ x⊔r≡x rewrite x⊔r≡x = here refl
  ... | inj₂ x⊔r≡r rewrite x⊔r≡r = there max∈xs

  ∈⇒≤max : ∀ {x xs} → x ∈ xs → x ≤ max xs
  ∈⇒≤max {x} {_ ∷ xs} (here refl) = m≤m⊔n x (max xs)
  ∈⇒≤max {x} {y ∷ xs} (there x∈xs) = ≤-trans (∈⇒≤max x∈xs) (n≤m⊔n y (max xs))
