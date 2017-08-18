open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (tabulate)
open import Data.List.All.Properties using (tabulate⁺)
open import Data.Product using (∄; ∃; ∃₂; _×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Dec using (¬∀⟶∃¬)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Algebra.FunctionProperties using (Selective)
open import Function using (_∘_)

open import RoutingLib.Algebra.FunctionProperties using (_×-Preserves_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_)
open import RoutingLib.Data.Graph.SimplePath using ([]; [_]; _∷_∣_; _∺_∣_; edge-∺; edge-∷; _∉𝔾_; _∈𝔾_; source) renaming (_≈_ to _≈ₚ_; _≉_ to _≉ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (ℙₛ; _∈𝔾?_; weight-cong; _≤ₚ?_; _∉?_) renaming (_≟_ to _≟ₚ_; ≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym; ∈𝔾-resp-≈ to ∈𝔾-resp-≈ₚ)
open import RoutingLib.Data.List.Properties using (foldr-map-commute; foldr-×preserves)
open import RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions using (SufficientConditions)
import RoutingLib.Routing.BellmanFord.PathsConvergence.Prelude as Prelude

module RoutingLib.Routing.BellmanFord.PathsConvergence.InconsistentPathProperties
  {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where
  
  open Prelude 𝓡𝓐 ⊕-sel G


















