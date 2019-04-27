--------------------------------------------------------------------------
-- Agda routing library
--
-- A proof that if F is a dynamic AMCO then F is also a dynamic ACO.
--------------------------------------------------------------------------

open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Relation.Unary using (Pred; _∈_)

open import RoutingLib.Iteration.Asynchronous.Dynamic using (AsyncIterable; Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (PartialACO; PartialAMCO)

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO
  {a ℓ n} {I∥ : AsyncIterable a ℓ n}
  {q} {Q : Pred (Subset n) q}
  (amco : PartialAMCO I∥ Q) where

open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
open import Level using (Lift; lift; lower) renaming (zero to 0ℓ)
open import Relation.Binary using (Rel; Decidable; _Respects_; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]≤x; x≤max[t]; max-cong)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (m+[n∸o]≤[m+n]∸o)
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.PropositionalEquality using (inspect′)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEquality
import RoutingLib.Function.Reasoning as FunctionReasoning

open import RoutingLib.Iteration.Asynchronous.Dynamic.Properties using (xy∈Aₚ∧x≈ₚy⇒x≈y)

open ≤-Reasoning

open AsyncIterable I∥
open PartialAMCO amco

----------------------------------------------
-- Export and define some useful properties --
----------------------------------------------

abstract

  inactiveEq : ∀ p {x y} → x ∈ Accordant p → y ∈ Accordant p → x ≈[ p ] y → x ≈ y
  inactiveEq p x∈Aₚ y∈Aₚ x≈ₚy i with i ∈? p
  ... | yes i∈p = x≈ₚy i∈p
  ... | no  i∉p = ≈ᵢ-trans (x∈Aₚ i∉p) (≈ᵢ-sym (y∈Aₚ i∉p))

module _ (e : Epoch) {p : Subset n} .(p∈Q : p ∈ Q) where

  dₘₐₓ : ℕ
  dₘₐₓ = proj₁ (dᵢ-bounded e p∈Q)

  dᵢ≤dₘₐₓ : ∀ {i} (x y : Sᵢ i) → dᵢ e p∈Q x y ≤ dₘₐₓ
  dᵢ≤dₘₐₓ = proj₂ (dᵢ-bounded e p∈Q)

  dₛᵢ-cong : ∀ {i} → dₛᵢ e p∈Q {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
  dₛᵢ-cong {i} with i ∈? p
  ... | yes i∈p = dᵢ-cong e p∈Q
  ... | no  i∉p = λ _ _ → refl

  d-cong : d e p∈Q Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  d-cong x≈y u≈v = max-cong refl (λ i → dₛᵢ-cong (x≈y i) (u≈v i))

  i∈p⇒dₛᵢ≡dᵢ : ∀ {i} (x y : Sᵢ i) → i ∈ₛ p → dₛᵢ e p∈Q x y ≡ dᵢ e p∈Q x y
  i∈p⇒dₛᵢ≡dᵢ {i} x y i∈p with i ∈? p
  ... | yes _   = refl
  ... | no  i∉p = contradiction i∈p i∉p

  dₛᵢ≤dᵢ : ∀ {i} (x y : Sᵢ i) → dₛᵢ e p∈Q x y ≤ dᵢ e p∈Q x y
  dₛᵢ≤dᵢ {i} x y with i ∈? p
  ... | yes _ = ≤-refl
  ... | no  _ = z≤n

  dᵢ≤d : ∀ x y {i} → i ∈ₛ p → dᵢ e p∈Q (x i) (y i) ≤ d e p∈Q x y
  dᵢ≤d x y {i} i∈p = x≤max[t] 0 _ (inj₂ (i , ≤-reflexive (sym (i∈p⇒dₛᵢ≡dᵢ (x i) (y i) i∈p))))

  d≤dₘₐₓ : ∀ x y → d e p∈Q x y ≤ dₘₐₓ
  d≤dₘₐₓ x y = max[t]≤x z≤n (λ i → ≤-trans (dₛᵢ≤dᵢ (x i) (y i)) (dᵢ≤dₘₐₓ (x i) (y i)))

---------------------
-- The biggest box --
---------------------

  abstract

    k* : ℕ
    k* = dₘₐₓ

    dᵢ≤k* : ∀ {i} (x y : Sᵢ i) → dᵢ e p∈Q x y ≤ k*
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

    dᵢ≤r[0] : ∀ {i} (x y : Sᵢ i) → dᵢ e p∈Q x y ≤ r[ 0 ]
    dᵢ≤r[0] x y = dᵢ≤dₘₐₓ x y

    d≤r[0] : ∀ x y → d e p∈Q x y ≤ r[ 0 ]
    d≤r[0] x y = d≤dₘₐₓ x y


------------------------------
-- Existence of fixed point --
------------------------------

module _ (e : Epoch) {p : Subset n} .(p∈Q : p ∈ Q) where

  abstract
  
    private

      f : S → S
      f = F e p

      fixedPoint : S → ∃ (λ x → f x ≈ x)
      fixedPoint v = inner (F-inactive e p∈Q v) (<-wellFounded (d e p∈Q (f v) (f (f v))))
        where
        inner : ∀ {x} → x ∈ Accordant p → Acc _<_ (d e p∈Q x (f x)) → ∃ (λ x* → f x* ≈ x*)
        inner {x} x∈Aₚ (acc x-acc) with F e p x ≟[ p ] x
        ... | yes fx≈ₚx = x , inactiveEq p (F-inactive e p∈Q x) x∈Aₚ fx≈ₚx
        ... | no  fx≉ₚx = inner (F-inactive e p∈Q x) (x-acc _ (F-strContrOnOrbits p∈Q x∈Aₚ fx≉ₚx))

    x* : S
    x* = proj₁ (fixedPoint ⊥)

    Fx*≈x* : F e p x* ≈ x*
    Fx*≈x* = proj₂ (fixedPoint ⊥)

    Fx*≈ₚx* : F e p x* ≈[ p ] x*
    Fx*≈ₚx* = ≈⇒≈ₛ Fx*≈x*

    x*-wellFormed : ∀ {i} → i ∉ₛ p → x* i ≈ᵢ ⊥ i
    x*-wellFormed {i} i∉p = ≈ᵢ-trans (≈ᵢ-sym (Fx*≈x* i)) (F-inactive e p∈Q x* i∉p)

-----------
-- Boxes --
-----------
-- Definition and properties of the subboxes B

B₀ : IPred Sᵢ 0ℓ
B₀ = Uᵢ

B : Epoch → {p : Subset n} → .(p ∈ Q) → ℕ → IPred Sᵢ _
B e {p} p∈Q zero    i xᵢ = Lift ℓ ⊤
B e {p} p∈Q (suc k) i xᵢ with i ∈? p
... | yes i∈p = Lift ℓ (dᵢ e p∈Q (x* e p∈Q i) xᵢ ≤ r[_] e p∈Q (suc k))
... | no  i∉p = xᵢ ≈ᵢ ⊥ i

B₀-eqᵢ : ∀ {e p} (p∈Q : p ∈ Q) → B₀ ≋ᵢ B e p∈Q 0
B₀-eqᵢ p∈Q = (λ _ → lift tt) , (λ _ → tt)

B-cong : ∀ {e p} (p∈Q : p ∈ Q) → ∀ {k i} → (_∈ B e p∈Q k i) Respects _≈ᵢ_
B-cong {e} {p} p∈Q {zero}  {i} _   _ = lift tt
B-cong {e} {p} p∈Q {suc k} {i} {x} {y} x≈y x∈B with i ∈? p
... | no  i∉p = ≈ᵢ-trans (≈ᵢ-sym x≈y) x∈B
... | yes i∈p = lift (begin
  dᵢ e p∈Q (x* e p∈Q i) y ≡⟨ dᵢ-cong e p∈Q ≈ᵢ-refl (≈ᵢ-sym x≈y) ⟩
  dᵢ e p∈Q (x* e p∈Q i) x ≤⟨ lower x∈B ⟩
  r[_] e p∈Q (suc k)     ∎)

B-null : ∀ {e p} (p∈Q : p ∈ Q) → ∀ {k i} → i ∉ₛ p → ⊥ i ∈ B e p∈Q k i
B-null {e} {p} _   {zero}  {i} _ = lift tt
B-null {e} {p} p∈Q {suc k} {i} i∉p with i ∈? p
... | yes i∈p = contradiction i∈p i∉p
... | no  _   = ≈ᵢ-refl

B-finish : ∀ e {p} (p∈Q : p ∈ Q) → ∃₂ λ k* x* → ∀ {k} → k* ≤ k →
             (x* ∈ᵢ B e p∈Q k × (∀ {x} → x ∈ᵢ B e p∈Q k → x ≈ x*))
B-finish e {p} p∈Q = k* e p∈Q , x* e p∈Q , λ k*≤k → x*∈B[k] k*≤k , x∈B[k]⇒x*≈x k*≤k
  where
  x∈B[k]⇒x*≈x : ∀ {k} → k* e p∈Q ≤ k → ∀ {x} → x ∈ᵢ B e p∈Q k → x ≈ x* e p∈Q
  x∈B[k]⇒x*≈x {zero}  k*≤0   {x} x∈B[k] i = dᵢ≡0⇒x≈y e p∈Q (n≤0⇒n≡0 (≤-trans (dᵢ≤k* e p∈Q (x i) _) k*≤0))
  x∈B[k]⇒x*≈x {suc k} k*≤1+k {x} x∈B[k] i with x∈B[k] i
  ... | xᵢ∈B with i ∈? p
  ...   | no i∉p = ≈ᵢ-trans xᵢ∈B (≈ᵢ-sym (x*-wellFormed e p∈Q i∉p))
  ...   | yes _  = ≈ᵢ-sym (dᵢ≡0⇒x≈y e p∈Q (n≤0⇒n≡0 (begin
    dᵢ e p∈Q (x* e p∈Q i) (x i) ≤⟨ lower xᵢ∈B ⟩
    r[_] e p∈Q (suc k)       ≡⟨ k*≤k⇒r[k]≡0 e p∈Q k*≤1+k ⟩
    0                        ∎)))

  x*∈B[k] : ∀ {k} → k* e p∈Q ≤ k → x* e p∈Q ∈ᵢ B e p∈Q k
  x*∈B[k] {zero}  k*≤k i = lift tt
  x*∈B[k] {suc k} k*≤k i with i ∈? p
  ... | yes _   = lift (subst (_≤ r[_] e p∈Q (suc k)) (sym (x≈y⇒dᵢ≡0 e p∈Q ≈ᵢ-refl)) z≤n)
  ... | no  i∉p = x*-wellFormed e p∈Q i∉p


∈Bᵢ⇒dᵢ≤r : ∀ {e p b i xᵢ} (p∈Q : p ∈ Q) → xᵢ ∈ B e p∈Q (suc b) i → dₛᵢ e p∈Q (x* e p∈Q i) xᵢ ≤ r[_] e p∈Q (suc b)
∈Bᵢ⇒dᵢ≤r {e} {p} {b} {i} {xᵢ} p∈Q xᵢ∈B with i ∈? p
... | yes _ = lower xᵢ∈B
... | no  _ = z≤n

∈B⇒d≤r : ∀ {e p b x} (p∈Q : p ∈ Q) → x ∈ᵢ B e p∈Q b → d e p∈Q (x* e p∈Q) x ≤ r[_] e p∈Q b
∈B⇒d≤r {e} {p} {zero}  {x} p∈Q x∈B = d≤r[0] e p∈Q (x* e p∈Q) x
∈B⇒d≤r {e} {p} {suc b} {x} p∈Q x∈B = max[t]≤x z≤n (λ i → ∈Bᵢ⇒dᵢ≤r p∈Q (x∈B i))

F-mono-B  : ∀ {e p} (p∈Q : p ∈ Q) → ∀ {k x} → x ∈ Accordant p → x ∈ᵢ B e p∈Q k → F e p x ∈ᵢ B e p∈Q (suc k)
F-mono-B {e} {p} p∈Q {k} {x} x∈Aₚ x∈B i with i ∈? p
... | no  i∉p = F-inactive e p∈Q x i∉p
... | yes i∈p with x ≟[ p ] x* e p∈Q
...   | yes x≈ₚx* = lift (begin
  dᵢ e p∈Q (x* e p∈Q i) (F e p x        i)   ≡⟨ dᵢ-cong e p∈Q ≈ᵢ-refl (F-cong e p (xy∈Aₚ∧x≈ₚy⇒x≈y I∥ x∈Aₚ (x*-wellFormed e p∈Q) x≈ₚx*) i∈p) ⟩
  dᵢ e p∈Q (x* e p∈Q i) (F e p (x* e p∈Q) i) ≡⟨ dᵢ-cong e p∈Q ≈ᵢ-refl (Fx*≈ₚx* e p∈Q i∈p) ⟩
  dᵢ e p∈Q (x* e p∈Q i) (x* e p∈Q i)         ≡⟨ x≈y⇒dᵢ≡0 e p∈Q ≈ᵢ-refl ⟩
  0                                          ≤⟨ z≤n ⟩
  r[_] e p∈Q (suc k)                         ∎)
...   | no  x≉ₚx* = lift (v<r[k]⇒v≤r[1+k] e p∈Q (begin-strict
  dᵢ e p∈Q (x* e p∈Q i) (F e p x i) ≤⟨ dᵢ≤d e p∈Q (x* e p∈Q) (F e p x) i∈p ⟩
  d e p∈Q (x* e p∈Q)   (F e p x)    <⟨ F-strContrOnFP p∈Q x∈Aₚ (Fx*≈x* e p∈Q) x≉ₚx* ⟩
  d e p∈Q (x* e p∈Q)    x           ≤⟨ ∈B⇒d≤r p∈Q x∈B ⟩
  r[_] e p∈Q k                      ∎))

----------------------
-- ACO construction --
----------------------

aco : PartialACO I∥ Uᵢ Q ℓ
aco = record
  { B₀-cong      = λ _ _ _ → tt
  ; F-resp-B₀    = λ _ _ _ → tt

  ; B            = B
  ; B₀-eqᵢ       = λ {e} → B₀-eqᵢ {e}
  ; Bᵢ-cong      = B-cong
  ; B-null       = B-null
  ; B-finish     = B-finish
  ; F-mono-B     = F-mono-B
  }




-----------------------------------------------------------------
-- Some hard-won knowledge on which box definitions don't work --
-----------------------------------------------------------------

-- Failure 1
--
-- B e p b i xᵢ = dₛᵢ p (x* e p i) xᵢ ≤ r[ b ]
--
-- causes the following lemma to fail when i ∉ p
--
-- x∈B[k*]⇒x*≈x : ∀ e p {x} → x ∈ᵢ B e p k* → x ≈ x* e p


-- Failure 2
--
-- B e p b i xᵢ with i ∈? p
-- ... | yes i∈p = Lift (dᵢ (x* e p i) xᵢ ≤ r[ suc b ])
-- ... | no  i∉p = xᵢ ≈ᵢ ⊥ i
--
-- causes the following lemma to fail
--
-- B₀-mono : ∀ {e f p q} → e ≤ f → B e p 0 ⊆[ Sᵢ ] B f q 0
