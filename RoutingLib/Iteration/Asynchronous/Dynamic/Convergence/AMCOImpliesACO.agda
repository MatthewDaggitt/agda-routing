--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that if F is a dynamic AMCO then F is also a dynamic ACO.
--------------------------------------------------------------------------

open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Lift; lift; lower) renaming (zero to 0ℓ)
open import Relation.Binary using (Rel; Decidable; _Respects_; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans)
open import Relation.Nullary using (yes; no)
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
open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (xy∈Aₚ∧x≈ₚy⇒x≈y)

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n} (open AsyncIterable I∥)
  {ℓ₁} {X : IPred Sᵢ ℓ₁} (X-valid : IsValidInitialSet I∥ X)
  {e : Epoch} {p : Subset n} 
  (localAMCO : LocalAMCO I∥ X e p) where

open IsValidInitialSet X-valid
open ≤-Reasoning

----------------------------------------------
-- Export and define some useful properties --
----------------------------------------------

inactiveEq : ∀ p {x y} → x ∈ Accordant p → y ∈ Accordant p → x ≈[ p ] y → x ≈ y
inactiveEq p x∈Aₚ y∈Aₚ x≈ₚy i with i ∈? p
... | yes i∈p = x≈ₚy i∈p
... | no  i∉p = ≈ᵢ-trans (x∈Aₚ i∉p) (≈ᵢ-sym (y∈Aₚ i∉p))


open LocalAMCO localAMCO

dₘₐₓ : ℕ
dₘₐₓ = proj₁ dᵢ-bounded

dᵢ≤dₘₐₓ : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ dₘₐₓ
dᵢ≤dₘₐₓ = proj₂ dᵢ-bounded

dₛᵢ-cong : ∀ {i} → dₛᵢ {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
dₛᵢ-cong {i} with i ∈? p
... | yes i∈p = dᵢ-cong
... | no  i∉p = λ _ _ → refl

d-cong : d Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
d-cong x≈y u≈v = max-cong refl (λ i → dₛᵢ-cong (x≈y i) (u≈v i))

i∈p⇒dₛᵢ≡dᵢ : ∀ {i} (x y : Sᵢ i) → i ∈ₛ p → dₛᵢ x y ≡ dᵢ x y
i∈p⇒dₛᵢ≡dᵢ {i} x y i∈p with i ∈? p
... | yes _   = refl
... | no  i∉p = contradiction i∈p i∉p

dₛᵢ≤dᵢ : ∀ {i} (x y : Sᵢ i) → dₛᵢ x y ≤ dᵢ x y
dₛᵢ≤dᵢ {i} x y with i ∈? p
... | yes _ = ≤-refl
... | no  _ = z≤n

dᵢ≤d : ∀ x y {i} → i ∈ₛ p → dᵢ (x i) (y i) ≤ d x y
dᵢ≤d x y {i} i∈p = x≤max[t] 0 _ (inj₂ (i , ≤-reflexive (sym (i∈p⇒dₛᵢ≡dᵢ (x i) (y i) i∈p))))

d≤dₘₐₓ : ∀ x y → d x y ≤ dₘₐₓ
d≤dₘₐₓ x y = max[t]≤x z≤n (λ i → ≤-trans (dₛᵢ≤dᵢ (x i) (y i)) (dᵢ≤dₘₐₓ (x i) (y i)))

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

  d≤r[0] : ∀ x y → d x y ≤ r[ 0 ]
  d≤r[0] x y = d≤dₘₐₓ x y

------------------------------
-- Existence of fixed point --
------------------------------

abstract
  private
    fixedPoint : ∃ (λ x* → F′ x* ≈ x* × x* ∈ᵢ X × x* ∈ Accordant p)
    fixedPoint = inner {⊥} (λ _ → ≈ᵢ-refl) ⊥∈X (<-wellFounded (d ⊥ (F′ ⊥)))
      where
      inner : ∀ {x} → x ∈ Accordant p → x ∈ᵢ X → Acc _<_ (d x (F′ x)) →
                ∃ (λ x* → F′ x* ≈ x* × x* ∈ᵢ X × x* ∈ Accordant p)
      inner {x} x∈Aₚ x∈X (acc x-acc) with F′ x ≟[ p ] x | F-pres-Aₚ x∈X x∈Aₚ
      ... | yes fx≈ₚx | Fx∈Aₚ = x , inactiveEq p Fx∈Aₚ x∈Aₚ fx≈ₚx , x∈X , x∈Aₚ
      ... | no  fx≉ₚx | Fx∈Aₚ = inner Fx∈Aₚ (F-pres-X x∈X) (x-acc _ (F-strContrOnOrbits x∈X x∈Aₚ fx≉ₚx))

  x* : S
  x* = proj₁ fixedPoint

  Fx*≈x* : F′ x* ≈ x*
  Fx*≈x* = proj₁ (proj₂ fixedPoint)

  Fx*≈ₚx* : F′ x* ≈[ p ] x*
  Fx*≈ₚx* = ≈⇒≈ₛ Fx*≈x*

  x*∈X : x* ∈ᵢ X
  x*∈X = proj₁ (proj₂ (proj₂ fixedPoint))

  x*∈Aₚ : x* ∈ Accordant p
  x*∈Aₚ = proj₂ (proj₂ (proj₂ fixedPoint))


-----------
-- Boxes --
-----------
-- Definition and properties of the subboxes B

B : ℕ → IPred Sᵢ _
B zero    i xᵢ = ⊤
B (suc k) i xᵢ with i ∈? p
... | yes i∈p = Lift ℓ (dᵢ (x* i) xᵢ ≤ r[ suc k ])
... | no  i∉p = xᵢ ≈ᵢ ⊥ i

B₀-universal : ∀ i x → x ∈ B 0 i
B₀-universal i x = _

B-cong : ∀ {k i} → (_∈ B k i) Respects _≈ᵢ_
B-cong {zero}  {i} _   _ = tt
B-cong {suc k} {i} {x} {y} x≈y x∈B with i ∈? p
... | no  i∉p = ≈ᵢ-trans (≈ᵢ-sym x≈y) x∈B
... | yes i∈p = lift (begin
  dᵢ (x* i) y  ≡⟨ dᵢ-cong ≈ᵢ-refl (≈ᵢ-sym x≈y) ⟩
  dᵢ (x* i) x  ≤⟨ lower x∈B ⟩
  r[ suc k ]   ∎)

B-null : ∀ {k i} → i ∉ₛ p → ⊥ i ∈ B k i
B-null {zero}  {i} _ = tt
B-null {suc k} {i} i∉p with i ∈? p
... | yes i∈p = contradiction i∈p i∉p
... | no  _   = ≈ᵢ-refl

B-finish : ∃₂ λ k* x* → x* ∈ᵢ X × (∀ {k} → k* ≤ k →
             (x* ∈ᵢ B k × (∀ {x} → x ∈ᵢ B k → x ≈ x*)))
B-finish = k* , x* , x*∈X , λ k*≤k → x*∈B[k] k*≤k , x∈B[k]⇒x*≈x k*≤k
  where
  x∈B[k]⇒x*≈x : ∀ {k} → k* ≤ k → ∀ {x} → x ∈ᵢ B k → x ≈ x*
  x∈B[k]⇒x*≈x {zero}  k*≤0   {x} x∈B[k] i = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (≤-trans (dᵢ≤k* (x i) _) k*≤0))
  x∈B[k]⇒x*≈x {suc k} k*≤1+k {x} x∈B[k] i with x∈B[k] i
  ... | xᵢ∈B with i ∈? p
  ...   | no i∉p = ≈ᵢ-trans xᵢ∈B (≈ᵢ-sym (x*∈Aₚ i∉p))
  ...   | yes _  = ≈ᵢ-sym (dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
    dᵢ (x* i) (x i)  ≤⟨ lower xᵢ∈B ⟩
    r[ suc k ]       ≡⟨ k*≤k⇒r[k]≡0 k*≤1+k ⟩
    0                ∎)))

  x*∈B[k] : ∀ {k} → k* ≤ k → x* ∈ᵢ B k
  x*∈B[k] {zero}  k*≤k i = tt
  x*∈B[k] {suc k} k*≤k i with i ∈? p
  ... | yes _   = lift (subst (_≤ r[ suc k ]) (sym (x≈y⇒dᵢ≡0 ≈ᵢ-refl)) z≤n)
  ... | no  i∉p = x*∈Aₚ i∉p


∈Bᵢ⇒dᵢ≤r : ∀ {b i xᵢ} → xᵢ ∈ B (suc b) i → dₛᵢ (x* i) xᵢ ≤ r[ suc b ]
∈Bᵢ⇒dᵢ≤r {b} {i} {xᵢ} xᵢ∈B with i ∈? p
... | yes _ = lower xᵢ∈B
... | no  _ = z≤n

∈B⇒d≤r : ∀ {b x} → x ∈ᵢ B b → d x* x ≤ r[ b ]
∈B⇒d≤r {zero}  {x} x∈B = d≤r[0] x* x
∈B⇒d≤r {suc b} {x} x∈B = max[t]≤x z≤n (λ i → ∈Bᵢ⇒dᵢ≤r (x∈B i))

F-mono-B  : ∀ {k x} → x ∈ᵢ X → x ∈ Accordant p → x ∈ᵢ B k → F′ x ∈ᵢ B (suc k)
F-mono-B {k} {x} x∈X x∈Aₚ x∈B i with i ∈? p
... | no  i∉p = F-pres-Aₚ x∈X x∈Aₚ i∉p
... | yes i∈p with x ≟[ p ] x*
...   | yes x≈ₚx* = lift (begin
  dᵢ (x* i) (F′ x  i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (F-cong e p (xy∈Aₚ∧x≈ₚy⇒x≈y I∥ x∈Aₚ x*∈Aₚ x≈ₚx*) i∈p) ⟩
  dᵢ (x* i) (F′ x* i)  ≡⟨ dᵢ-cong ≈ᵢ-refl (Fx*≈ₚx* i∈p) ⟩
  dᵢ (x* i) (x* i)     ≡⟨ x≈y⇒dᵢ≡0 ≈ᵢ-refl ⟩
  0                    ≤⟨ z≤n ⟩
  r[ suc k ]           ∎)
...   | no  x≉ₚx* = lift (v<r[k]⇒v≤r[1+k] (begin-strict
  dᵢ (x* i) (F′ x i)   ≤⟨ dᵢ≤d x* (F′ x) i∈p ⟩
  d x* (F′ x)          <⟨ F-strContrOnFP x∈X x∈Aₚ Fx*≈x* x≉ₚx* ⟩
  d x* x               ≤⟨ ∈B⇒d≤r x∈B ⟩
  r[ k ]               ∎))

X⊆B₀ : X ⊆ᵢ B 0
X⊆B₀ = _

localACO : LocalACO I∥ X e p ℓ
localACO = record
  { B         = B
  ; Bᵢ-cong   = λ {k} → B-cong {k}
  ; X⊆B₀      = X⊆B₀
  ; B-finish  = B-finish
  ; B-null    = λ {k} → B-null {k}
  ; F-mono-B  = F-mono-B
  }

-----------------------------------------------------------------
-- Some hard-won knowledge on which box definitions don't work --
-----------------------------------------------------------------

-- Failure 1
--
-- B b i xᵢ = dₛᵢ (x* i) xᵢ ≤ r[ b ]
--
-- causes the following lemma to fail when i ∉ p
--
-- x∈B[k*]⇒x*≈x : ∀ {x} → x ∈ᵢ B k* → x ≈ x*


-- Failure 2
--
-- B b i xᵢ with i ∈? p
-- ... | yes i∈p = Lift (dᵢ (x* i) xᵢ ≤ r[ suc b ])
-- ... | no  i∉p = xᵢ ≈ᵢ ⊥ i
--
-- causes the following lemma to fail
--
-- B₀-mono : ∀ {e f p q} → e ≤ f → B e p 0 ⊆[ Sᵢ ] B f q 0
