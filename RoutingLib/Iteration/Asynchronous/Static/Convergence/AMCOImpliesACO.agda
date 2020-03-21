--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that I∥ being an AMCO implies that I∥ is also an ACO. The same
-- result is also derived in:
--
--   `RoutingLib.Iteration.Asynchronous.Static.ToDynamic`
--
-- by going via dynamic iterations. This version of the proof is included
-- for the JAR 2019 paper submission.
--
-- It's also instructive to compare this with the dynamic proof in
-- `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO`
-- in order to appreciate how the addition of epochs and participants
-- complicate the proofs.
--------------------------------------------------------------------------

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable)
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions

module RoutingLib.Iteration.Asynchronous.Static.Convergence.AMCOImpliesACO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n}
  {p} {X₀ : IPred _ p}
  (amco : PartialAMCO I∥ X₀) where

open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Level using (Lift; lift; lower) renaming (zero to 0ℓ)
open import Relation.Binary using (Rel; Decidable; _Respects_; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Data.Nat.Properties using (m+[n∸o]≤[m+n]∸o)
open import RoutingLib.Data.Vec.Functional using (max)
open import RoutingLib.Data.Vec.Functional.Properties using (max[t]≤x; x≤max[t]; max-cong)
open import RoutingLib.Data.Vec.Functional.Membership.Propositional.Properties using (max[t]∈t)
import RoutingLib.Function.Metric.Construct.Condition as Condition
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEquality
import RoutingLib.Function.Reasoning as FunctionReasoning

open AsyncIterable I∥
open PartialAMCO amco
open ≤-Reasoning

----------------------------------------------
-- Export and define some useful properties --
----------------------------------------------

dₘₐₓ : ℕ
dₘₐₓ = max 0 (proj₁ ∘ dᵢ-bounded)

dᵢ≤dₘₐₓ : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ dₘₐₓ
dᵢ≤dₘₐₓ {i} x y = x≤max[t] 0 _ (inj₂ (i , proj₂ (dᵢ-bounded i) x y))

d-cong : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
d-cong x≈y u≈v = max-cong refl λ i → dᵢ-cong (x≈y i) (u≈v i)

dᵢ≤d : ∀ x y {i} → dᵢ (x i) (y i) ≤ d x y
dᵢ≤d x y {i} = x≤max[t] 0 _ (inj₂ (i , ≤-refl))

d≤dₘₐₓ : ∀ x y → d x y ≤ dₘₐₓ
d≤dₘₐₓ x y = max[t]≤x z≤n (λ i → dᵢ≤dₘₐₓ (x i) (y i))

---------------------
-- The biggest box --
---------------------

abstract

  k* : ℕ
  k* = dₘₐₓ

  dᵢ≤k* : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ k*
  dᵢ≤k* x y = dᵢ≤dₘₐₓ x y

---------------------------
-- Radius index function --
---------------------------

abstract

  r[_] : ℕ → ℕ
  r[ k ] = dₘₐₓ ∸ k

  v<r[k]⇒v≤r[1+k] : ∀ {v k} → v < r[ k ] → v ≤ r[ suc k ]
  v<r[k]⇒v≤r[1+k] {v} {k} v<r[k] = ≤-pred (begin
    suc v              ≤⟨ v<r[k] ⟩
    dₘₐₓ ∸ k           ≡⟨⟩
    suc dₘₐₓ ∸ suc k   ≤⟨ m+[n∸o]≤[m+n]∸o 1 dₘₐₓ (suc k) ⟩
    suc (dₘₐₓ ∸ suc k) ∎)

  k*≤k⇒r[k]≡0 : ∀ {k} → k* ≤ k → r[ k ] ≡ 0
  k*≤k⇒r[k]≡0 k*≤k = m≤n⇒m∸n≡0 k*≤k

  dᵢ≤r[0] : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ r[ 0 ]
  dᵢ≤r[0] x y = dᵢ≤dₘₐₓ x y

  d≤r[0] : ∀ x y → d x y ≤ r[ 0 ]
  d≤r[0] x y = d≤dₘₐₓ x y


------------------------------
-- Existence of fixed point --
------------------------------

abstract

  private

    f : S → S
    f = F

    fixedPoint : ∀ {v} → v ∈ᵢ X₀ → ∃ (λ x → f x ≈ x × x ∈ᵢ X₀)
    fixedPoint {v} v∈X₀ = inner v∈X₀ (<-wellFounded (d v (f v)))
      where
      inner : ∀ {x} → x ∈ᵢ X₀ → Acc _<_ (d x (f x)) → ∃ (λ x* → f x* ≈ x* × x* ∈ᵢ X₀)
      inner {x} x∈X₀ (acc x-acc) with F x ≟ x
      ... | yes fx≈x = x , fx≈x , x∈X₀
      ... | no  fx≉x = inner {F x} (X₀-closed x∈X₀) (x-acc _ (F-strContrOnOrbits x∈X₀ fx≉x))

  x* : S
  x* = proj₁ (fixedPoint element∈X₀)

  Fx*≈x* : F x* ≈ x*
  Fx*≈x* = proj₁ (proj₂ (fixedPoint element∈X₀))

  x*∈X₀ : x* ∈ᵢ X₀
  x*∈X₀ = proj₂ (proj₂ (fixedPoint element∈X₀))
  
-----------
-- Boxes --
-----------
-- Definition and properties of the subboxes B

B : ℕ → IPred Sᵢ p
B k i xᵢ = (xᵢ ∈ X₀ i) × (dᵢ (x* i) xᵢ ≤ r[ k ])

Bᵢ-cong : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
Bᵢ-cong {k} {i} {x} {y} x≈y (x∈X₀ , x≤r[k]) = X₀-cong x≈y x∈X₀ , (begin
  dᵢ (x* i) y ≡⟨ dᵢ-cong ≈ᵢ-refl (≈ᵢ-sym x≈y) ⟩
  dᵢ (x* i) x ≤⟨ x≤r[k] ⟩
  r[ k ]      ∎)

B-finish : ∀ {k} → k* ≤ k → (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≈ x*))
B-finish k*≤k = x*∈B[k] k*≤k , x∈B[k]⇒x*≈x k*≤k
  where
  x∈B[k]⇒x*≈x : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  x∈B[k]⇒x*≈x {zero}  k*≤0   {x} x∈B[k] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (≤-trans (dᵢ≤k* (x i) _) k*≤0))
  x∈B[k]⇒x*≈x {suc k} k*≤1+k {x} x∈B[k] i with x∈B[k] i
  ... | _ , xᵢ∈B = ≈ᵢ-sym (dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
    dᵢ (x* i) (x i)  ≤⟨ xᵢ∈B ⟩
    r[ suc k ]       ≡⟨ k*≤k⇒r[k]≡0 k*≤1+k ⟩
    0                ∎)))

  x*∈B[k] : ∀ {k} → k* ≤ k → x* ∈ᵢ B k
  x*∈B[k] {k} k*≤k i = x*∈X₀ i , subst (_≤ r[ k ]) (sym (x≈y⇒dᵢ≡0 ≈ᵢ-refl)) z≤n

∈B⇒d≤r : ∀ {k x} → x ∈ᵢ B k → d x* x ≤ r[ k ]
∈B⇒d≤r {zero}  {x} _ = d≤r[0] x* x
∈B⇒d≤r {suc k} {x} x∈B = max[t]≤x z≤n (proj₂ ∘ x∈B)

F-resp-B₀ : ∀ {x} → x ∈ᵢ B 0 → F x ∈ᵢ B 0
F-resp-B₀ x∈B₀ i = X₀-closed (proj₁ ∘ x∈B₀) i , dᵢ≤r[0] _ _

F-mono-B  : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
F-mono-B {k} {x} x∈B i with x ≟ x*
...   | yes x≈x* = X₀-closed (proj₁ ∘ x∈B) i , (begin
  dᵢ (x* i) (F x  i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (F-cong x≈x* i) ⟩
  dᵢ (x* i) (F x* i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (Fx*≈x* i) ⟩
  dᵢ (x* i) (x*   i)  ≡⟨ x≈y⇒dᵢ≡0 ≈ᵢ-refl ⟩
  0                   ≤⟨ z≤n ⟩
  r[ suc k ]          ∎)
...   | no  x≉x* = X₀-closed (proj₁ ∘ x∈B) i , (v<r[k]⇒v≤r[1+k] (begin-strict
  dᵢ (x* i) (F x i) ≤⟨ dᵢ≤d x* (F x) ⟩
  d x*   (F x)      <⟨ F-strContrOnFP Fx*≈x* (proj₁ ∘ x∈B) x≉x* ⟩
  d x*    x         ≤⟨ ∈B⇒d≤r x∈B ⟩
  r[ k ]            ∎))

X₀⊆B₀ : X₀ ⊆ᵢ B 0
X₀⊆B₀ x∈X₀ = x∈X₀ , dᵢ≤r[0] _ _

B₀⊆X₀ : B 0 ⊆ᵢ X₀
B₀⊆X₀ (x∈X₀ , _) = x∈X₀

X₀≋B₀ : X₀ ≋ᵢ B 0
X₀≋B₀ = X₀⊆B₀ , B₀⊆X₀

----------------------
-- ACO construction --
----------------------

aco : PartialACO I∥ X₀ p
aco = record
  { B            = B
  ; Bᵢ-cong      = Bᵢ-cong
  ; F-resp-B₀    = F-resp-B₀
  ; F-mono-B     = F-mono-B
  ; x*           = x*
  ; k*           = k*
  ; B-finish     = B-finish
  ; X₀≋B₀        = X₀≋B₀
  }
