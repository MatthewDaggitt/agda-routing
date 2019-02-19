open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred)
open import Data.Nat.Properties hiding (module ≤-Reasoning; _≟_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using (Lift; lift; lower) renaming (zero to 0ℓ)
open import Relation.Binary using (Rel; Decidable; _Respects_; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]≤x; x≤max[t]; max-cong)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (m+[n∸o]≤[m+n]∸o; module ≤-Reasoning)
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.PropositionalEquality using (inspect′)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEquality
import RoutingLib.Function.Reasoning as FunctionReasoning

open import RoutingLib.Iteration.Asynchronous.Static using (AsyncIterable)
open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions using (ACO; AMCO)

open ≤-Reasoning

module RoutingLib.Iteration.Asynchronous.Static.Convergence.AMCOImpliesACO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n}
  (amco : AMCO I∥) where

open AsyncIterable I∥
open AMCO amco

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

    fixedPoint : S → ∃ (λ x → f x ≈ x)
    fixedPoint v = inner v (<-wellFounded (d v (f v)))
      where
      inner : ∀ x → Acc _<_ (d x (f x)) → ∃ (λ x* → f x* ≈ x*)
      inner x (acc x-acc) with F x ≟ x
      ... | yes fx≈x = x , fx≈x
      ... | no  fx≉x = inner (F x) (x-acc _ (F-strContrOnOrbits fx≉x))

  x* : S
  x* = proj₁ (fixedPoint element)

  Fx*≈x* : F x* ≈ x*
  Fx*≈x* = proj₂ (fixedPoint element)

-----------
-- Boxes --
-----------
-- Definition and properties of the subboxes B

B : ℕ → IPred Sᵢ 0ℓ
B k i xᵢ = dᵢ (x* i) xᵢ ≤ r[ k ]

B₀-universal : ∀ i x → x ∈ B 0 i
B₀-universal i x = dᵢ≤r[0] (x* i) x

Bᵢ-cong : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
Bᵢ-cong {k} {i} {x} {y} x≈y x∈B = begin
  dᵢ (x* i) y ≡⟨ dᵢ-cong ≈ᵢ-refl (≈ᵢ-sym x≈y) ⟩
  dᵢ (x* i) x ≤⟨ x∈B ⟩
  r[ k ]      ∎

B-finish : ∀ {k} → k* ≤ k → (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≈ x*))
B-finish k*≤k = x*∈B[k] k*≤k , x∈B[k]⇒x*≈x k*≤k
  where
  x∈B[k]⇒x*≈x : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  x∈B[k]⇒x*≈x {zero}  k*≤0   {x} x∈B[k] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (≤-trans (dᵢ≤k* (x i) _) k*≤0))
  x∈B[k]⇒x*≈x {suc k} k*≤1+k {x} x∈B[k] i with x∈B[k] i
  ... | xᵢ∈B = ≈ᵢ-sym (dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
    dᵢ (x* i) (x i)  ≤⟨ xᵢ∈B ⟩
    r[ suc k ]       ≡⟨ k*≤k⇒r[k]≡0 k*≤1+k ⟩
    0                ∎)))

  x*∈B[k] : ∀ {k} → k* ≤ k → x* ∈ᵢ B k
  x*∈B[k] {k} k*≤k i = subst (_≤ r[ k ]) (sym (x≈y⇒dᵢ≡0 ≈ᵢ-refl)) z≤n

∈B⇒d≤r : ∀ {k x} → x ∈ᵢ B k → d x* x ≤ r[ k ]
∈B⇒d≤r {zero}  {x} x∈B = d≤r[0] x* x
∈B⇒d≤r {suc k} {x} x∈B = max[t]≤x z≤n x∈B

F-mono-B  : ∀ {k x} → x ∈ᵢ B k → F x ∈ᵢ B (suc k)
F-mono-B {k} {x} x∈B i with x ≟ x*
...   | yes x≈x* = begin
  dᵢ (x* i) (F x  i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (F-cong x≈x* i) ⟩
  dᵢ (x* i) (F x* i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (Fx*≈x* i) ⟩
  dᵢ (x* i) (x*   i)  ≡⟨ x≈y⇒dᵢ≡0 ≈ᵢ-refl ⟩
  0                   ≤⟨ z≤n ⟩
  r[ suc k ]          ∎
...   | no  x≉x* = v<r[k]⇒v≤r[1+k] (begin
  dᵢ (x* i) (F x i) ≤⟨ dᵢ≤d x* (F x) ⟩
  d x*   (F x)      <⟨ F-strContrOnFP Fx*≈x* x≉x* ⟩
  d x*    x         ≤⟨ ∈B⇒d≤r x∈B ⟩
  r[ k ]            ∎)

----------------------
-- ACO construction --
----------------------

aco : ACO I∥ 0ℓ
aco = record
  { B            = B
  ; Bᵢ-cong       = Bᵢ-cong
  ; B₀-universal = B₀-universal
  ; F-mono-B     = F-mono-B
  ; x*           = x*
  ; k*           = k*
  ; B-finish     = B-finish
  }
