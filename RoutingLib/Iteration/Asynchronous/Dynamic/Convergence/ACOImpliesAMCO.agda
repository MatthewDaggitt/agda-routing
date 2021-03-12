--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that if F is a dynamic ACO then F is also a dynamic AMCO.
--------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred; _⊔_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Lift; lift; lower) renaming (zero to 0ℓ)
open import Function.Metric.Nat
open import Relation.Binary using (Rel; Decidable; _Respects_; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Data.Vec.Functional using (max)
open import RoutingLib.Data.Vec.Functional.Properties using (max[t]≤x; x≤max[t]; max-cong)
open import RoutingLib.Data.Vec.Functional.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (m+[n∸o]≤[m+n]∸o)
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Unary.Indexed
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEquality
import RoutingLib.Function.Reasoning as FunctionReasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic using (AsyncIterable; Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Properties.ACO as ACOProperties
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (xy∈Aₚ∧x≈ₚy⇒x≈y)

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesAMCO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n} (open AsyncIterable I∥)
  {ℓ₁} {X : IPred Sᵢ ℓ₁} (X-valid : IsValidInitialSet I∥ X)
  {e : Epoch} {p : Subset n}
  {ℓ₂} (localACO : LocalACO I∥ X e p ℓ₂) where

open IsValidInitialSet X-valid
open ≤-Reasoning
open LocalACO localACO
open ACOProperties localACO

private
  variable
    i : Fin n
    w x y z : Sᵢ i

postulate _∈B?_ : ∀ {i} x k → Dec (x ∈ B k i)

box : Sᵢ i → ℕ → ℕ
box x zero = zero
box x (suc k) with x ∈B? (suc k)
... | yes _ = suc k
... | no  _ = box x k

dᵢ : Sᵢ i → Sᵢ i → ℕ
dᵢ x y with x ≟ᵢ y
... | yes _ = 0
... | no  _ = suc ((k* ∸ box x k*) ⊔ (k* ∸ box y k*))

dᵢ-cong : w ≈ᵢ x → y ≈ᵢ z → dᵢ w y ≡ dᵢ x z
dᵢ-cong {w = w} {x} {y} {z} w≈x y≈z with w ≟ᵢ y | x ≟ᵢ z
... | yes _   | yes _   = refl
... | yes _   | no  _   = {!!}
... | no  w≉y | yes x≈z = {!!}
... | no  _   | no  _   = {!cong suc ?!}

x≈y⇒dᵢxy≡0 : x ≈ᵢ y → dᵢ x y ≡ 0
x≈y⇒dᵢxy≡0 {x = x} {y} x≈y with x ≟ᵢ y
... | yes _   = refl
... | no  x≉y = contradiction x≈y x≉y

dᵢxy≡0⇒x≈y : dᵢ x y ≡ 0 → x ≈ᵢ y
dᵢxy≡0⇒x≈y {x = x} {y} dxy≡0 with x ≟ᵢ y
... | yes x≈y = x≈y
... | no  _   = contradiction dxy≡0 λ()

dᵢ-isQuasiSemiMetric : ∀ i → IsQuasiSemiMetric {A = Sᵢ i} _≈ᵢ_ dᵢ
dᵢ-isQuasiSemiMetric i = record
  { isPreMetric = record
    { isProtoMetric = record
       { isPartialOrder  = ≤-isPartialOrder
       ; ≈-isEquivalence = {!≈-isEquivalenceᵢ!}
       ; cong            = {!!}
       ; nonNegative     = z≤n
       }
    ; ≈⇒0           = x≈y⇒dᵢxy≡0
    }
  ; 0⇒≈         = dᵢxy≡0⇒x≈y
  }

dᵢ-bounded : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ suc k*
dᵢ-bounded x y with x ≟ᵢ y
... | yes _ = z≤n
... | no  _ = s≤s (⊔-pres-≤m (m∸n≤m k* (box x k*)) (m∸n≤m k* (box y k*)))

localAMCO : LocalAMCO I∥ X e p
localAMCO = record
  { dᵢ                   = dᵢ
  ; dᵢ-isQuasiSemiMetric = {!!}
  ; dᵢ-bounded           = suc k* , dᵢ-bounded
  ; F-strContrOnOrbits   = {!!}
  ; F-strContrOnFP       = {!!}
  ; F-pres-Aₚ            = {!!}
  }
