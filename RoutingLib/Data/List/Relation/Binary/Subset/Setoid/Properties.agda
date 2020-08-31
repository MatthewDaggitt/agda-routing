open import Data.List using ([]; _∷_; filter)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary using (Setoid)
open import Relation.Unary as U using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

module RoutingLib.Data.List.Relation.Binary.Subset.Setoid.Properties where

  module _ {c ℓ} (S : Setoid c ℓ) where

    open Setoid S renaming (Carrier to A)
    open import Data.List.Relation.Binary.Subset.Setoid S

    ⊆-filter : ∀ {p} {P : A → Set p} (P? : Decidable P)
                 {q} {Q : A → Set q} (Q? : Decidable Q) →
                 P U.⊆ Q → ∀ xs → filter P? xs ⊆ filter Q? xs
    ⊆-filter P? Q? P⋐Q []       ()
    ⊆-filter P? Q? P⋐Q (x ∷ xs) v∈f[x∷xs] with P? x | Q? x
    ... | no  _  | no  _  = ⊆-filter P? Q? P⋐Q xs v∈f[x∷xs]
    ... | yes Px | no ¬Qx = contradiction (P⋐Q Px) ¬Qx
    ... | no  _  | yes _  = there (⊆-filter P? Q? P⋐Q xs v∈f[x∷xs])
    ... | yes _  | yes _  with v∈f[x∷xs]
    ...   | here  v≈x     = here v≈x
    ...   | there v∈f[xs] = there (⊆-filter P? Q? P⋐Q xs v∈f[xs])
