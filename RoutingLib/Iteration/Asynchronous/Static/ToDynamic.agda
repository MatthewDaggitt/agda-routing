open import Data.Fin using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (Subset; _∈_)
open import Data.Maybe using (Maybe; just; nothing; to-witness; Is-just)
open import Data.Unit using (tt)
open import Data.Product using ()
open import Function using (_∘_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Indexed.Homogeneous hiding (Rel)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Maybe.Properties
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset as FiniteSubset

import RoutingLib.Iteration.Asynchronous.Dynamic as Dynamic
import RoutingLib.Iteration.Asynchronous.Static as Static
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule

module RoutingLib.Iteration.Asynchronous.Static.ToDynamic
  {a ℓ n} (𝓘 : Static.AsyncIterable a ℓ n) where

open Static.AsyncIterable 𝓘
  
------------------------------------------------------------------------
-- Formulating the iteration

Sᵢ′ : Fin n → Set a
Sᵢ′ i = Maybe (Sᵢ i)

S′ : Set a
S′ = ∀ i → Sᵢ′ i

data _≈ᵢ′_ : IRel Sᵢ′ ℓ where
  nothing : ∀ {i} → _≈ᵢ′_ {i} nothing nothing
  just    : ∀ {i} {x y : Sᵢ i} → x ≈ᵢ y → just x ≈ᵢ′ just y

_≈′_ : Rel S′ ℓ
x ≈′ y = ∀ i → x i ≈ᵢ′ y i

≈ᵢ′-refl : Reflexive Sᵢ′ _≈ᵢ′_
≈ᵢ′-refl {_} {just x}  = just ≈ᵢ-refl
≈ᵢ′-refl {_} {nothing} = nothing

≈ᵢ′-sym : Symmetric Sᵢ′ _≈ᵢ′_
≈ᵢ′-sym nothing    = nothing
≈ᵢ′-sym (just x≈y) = just (≈ᵢ-sym x≈y)

≈ᵢ′-trans : Transitive Sᵢ′ _≈ᵢ′_
≈ᵢ′-trans nothing    nothing    = nothing
≈ᵢ′-trans (just x≈y) (just y≈z) = just (≈ᵢ-trans x≈y y≈z)

_≟ᵢ′_ : Decidable Sᵢ′ _≈ᵢ′_
nothing ≟ᵢ′ nothing = yes nothing
nothing ≟ᵢ′ just y  = no λ ()
just x  ≟ᵢ′ nothing = no λ ()
just x  ≟ᵢ′ just y  with x ≟ᵢ y
... | yes x≈y = yes (just x≈y)
... | no  x≉y = no λ {(just x≈y) → x≉y x≈y}

≈ᵢ′-isEquivalenceᵢ : IsIndexedEquivalence Sᵢ′ _≈ᵢ′_
≈ᵢ′-isEquivalenceᵢ = record
  { reflᵢ  = ≈ᵢ′-refl
  ; symᵢ   = ≈ᵢ′-sym
  ; transᵢ = ≈ᵢ′-trans
  }

≈ᵢ′-isDecEquivalenceᵢ : IsIndexedDecEquivalence Sᵢ′ _≈ᵢ′_
≈ᵢ′-isDecEquivalenceᵢ = record
  { _≟ᵢ_           = _≟ᵢ′_
  ; isEquivalenceᵢ = ≈ᵢ′-isEquivalenceᵢ
  }

⊥′ : S′
⊥′ i = nothing

open FiniteSubset Sᵢ′ _≈ᵢ′_ using () renaming (_∼[_]_ to _≈[_]_) public

Valid : Subset n → S′ → Fin n → Set a
Valid p x i = i ∈ p → Is-just (x i)

Valid? : ∀ p x i → Dec (Valid p x i)
Valid? = {!!}

F′ : Epoch → Subset n → S′ → S′ 
F′ e p x i with all? (IsJust? ∘ x)
... | yes xⱼ = just (F (to-witness ∘ xⱼ) i)
... | no  _  = nothing

IsJust-cong : ∀ {i} {x y : Sᵢ′ i} → x ≈ᵢ′ y → Is-just x → Is-just y
IsJust-cong (just x≈y) (just tt) = just tt

toWitness-cong : ∀ {i} {x y : Sᵢ′ i} → x ≈ᵢ′ y → (xⱼ : Is-just x) (yⱼ : Is-just y) →
                 to-witness xⱼ ≈ᵢ to-witness yⱼ
toWitness-cong = {!!}

F′-cong : ∀ e p {x y} → x ≈[ p ] y → F′ e p x ≈[ p ] F′ e p y
F′-cong e p {x} {y} x≈ₚy {i} i∈p with all? (IsJust? ∘ x) | all? (IsJust? ∘ y)
... | yes xⱼ | yes yⱼ = just (F-cong (λ j → toWitness-cong (x≈ₚy {!!}) (xⱼ j) (yⱼ j)) i)
... | yes xⱼ | no ¬yⱼ = contradiction (λ j → IsJust-cong (x≈ₚy {!!}) (xⱼ j)) ¬yⱼ
... | no ¬xⱼ | yes yⱼ = contradiction (λ j → IsJust-cong (≈ᵢ′-sym (x≈ₚy {!!})) (yⱼ j)) ¬xⱼ
... | no  _  | no  _  = nothing

𝓘′ : Dynamic.IsAsyncIterable _≈ᵢ′_ F′ ⊥′
𝓘′ = record
  { isDecEquivalenceᵢ = ≈ᵢ′-isDecEquivalenceᵢ
  ; F-cong            = F′-cong
  }

------------------------------------------------------------------------
-- Formulating the iteration

asyncIter
