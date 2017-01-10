open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any as Any using (here; there)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (refl)
open Any.Membership-≡ using (_∈_; _∉_)


module RoutingLib.Data.List.SucMap where
  
  0∉mapₛ : ∀ {n} {xs : List (Fin n)} → fzero ∉ map fsuc xs
  0∉mapₛ {xs = []} = λ()
  0∉mapₛ {xs = x ∷ xs} (here ())
  0∉mapₛ {xs = x ∷ xs} (there 0∈xs) = 0∉mapₛ 0∈xs

  ∈-mapₛ : ∀ {n i} {xs : List (Fin n)} → fsuc i ∈ map fsuc xs → i ∈ xs
  ∈-mapₛ {xs = []} ()
  ∈-mapₛ {xs = x ∷ xs} (here refl) = here refl
  ∈-mapₛ {xs = x ∷ xs} (there s[i]∈map) = there (∈-mapₛ s[i]∈map)

  mapₛ-∈ : ∀ {n i} {xs : List (Fin n)} → i ∈ xs → fsuc i ∈ map fsuc xs
  mapₛ-∈ {xs = []} ()
  mapₛ-∈ {xs = x ∷ xs} (here refl) = here refl
  mapₛ-∈ {xs = x ∷ xs} (there i∈map) = there (mapₛ-∈ i∈map)
