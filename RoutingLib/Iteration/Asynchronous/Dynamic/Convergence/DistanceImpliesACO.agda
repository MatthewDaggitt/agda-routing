open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_; ⊤ to ⊤ₛ)
open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s; zero; suc; _+_; _∸_; ≤-pred)
open import Data.Nat.Properties hiding (module ≤-Reasoning)
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
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)

open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (max[t]≤x; x≤max[t]; max-cong)
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (max[t]∈t)
open import RoutingLib.Data.Nat.Properties using (m+[n∸o]≤[m+n]∸o; module ≤-Reasoning)
import RoutingLib.Function.Metric.Construct.Condition as Condition
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.PropositionalEquality using (inspect′)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construct.FiniteSubset.DecEquality as SubsetEquality

open import RoutingLib.Iteration.Asynchronous.Dynamic using (AsyncIterable; Epoch)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO; UltrametricConditions)

open ≤-Reasoning

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.DistanceImpliesACO
  {a ℓ n} {𝓘 : AsyncIterable a ℓ n} (UC : UltrametricConditions 𝓘) where

open AsyncIterable 𝓘
open UltrametricConditions UC

----------------------------------------------
-- Export and define some useful properties --
----------------------------------------------

abstract

  inactiveEq : ∀ p {x y} → WellFormed p x → WellFormed p y → x ≈[ p ] y → x ≈ y
  inactiveEq p ⊥x ⊥y x≈ₚy i with i ∈? p
  ... | yes i∈p = x≈ₚy i∈p
  ... | no  i∉p = ≈ᵢ-trans (⊥x i∉p) (≈ᵢ-sym (⊥y i∉p))

module _ (e : Epoch) (p : Subset n) where

  dₘₐₓ : ℕ
  dₘₐₓ = proj₁ (dᵢ-bounded e p)

  dᵢ≤dₘₐₓ : ∀ {i} (x y : Sᵢ i) → dᵢ e p x y ≤ dₘₐₓ
  dᵢ≤dₘₐₓ = proj₂ (dᵢ-bounded e p)
  
  dₛᵢ-cong : ∀ {i} → dₛᵢ e p {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
  dₛᵢ-cong {i} with i ∈? p
  ... | yes i∈p = dᵢ-cong e p
  ... | no  i∉p = λ _ _ → refl

  d-cong : d e p Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  d-cong x≈y u≈v = max-cong refl (λ i → dₛᵢ-cong (x≈y i) (u≈v i))
  
  i∈p⇒dₛᵢ≡dᵢ : ∀ {i} (x y : Sᵢ i) → i ∈ₛ p → dₛᵢ e p x y ≡ dᵢ e p x y 
  i∈p⇒dₛᵢ≡dᵢ {i} x y i∈p with i ∈? p
  ... | yes _   = refl
  ... | no  i∉p = contradiction i∈p i∉p

  dₛᵢ≤dᵢ : ∀ {i} (x y : Sᵢ i) → dₛᵢ e p x y ≤ dᵢ e p x y
  dₛᵢ≤dᵢ {i} x y with i ∈? p
  ... | yes _ = ≤-refl
  ... | no  _ = z≤n

  dᵢ≤d : ∀ x y {i} → i ∈ₛ p → dᵢ e p (x i) (y i) ≤ d e p x y
  dᵢ≤d x y {i} i∈p = x≤max[t] 0 _ (inj₂ (i , ≤-reflexive (sym (i∈p⇒dₛᵢ≡dᵢ (x i) (y i) i∈p))))

  d≤dₘₐₓ : ∀ x y → d e p x y ≤ dₘₐₓ
  d≤dₘₐₓ x y = max[t]≤x z≤n (λ i → ≤-trans (dₛᵢ≤dᵢ (x i) (y i)) (dᵢ≤dₘₐₓ (x i) (y i)))
  
---------------------
-- The biggest box --
---------------------

  abstract

    k* : ℕ
    k* = dₘₐₓ

    dᵢ≤k* : ∀ {i} (x y : Sᵢ i) → dᵢ e p x y ≤ k*
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

    dᵢ≤r[0] : ∀ {i} (x y : Sᵢ i) → dᵢ e p x y ≤ r[ 0 ]
    dᵢ≤r[0] x y = dᵢ≤dₘₐₓ x y

    d≤r[0] : ∀ x y → d e p x y ≤ r[ 0 ]
    d≤r[0] x y = d≤dₘₐₓ x y

------------------------------
-- Existence of fixed point --
------------------------------

  abstract
    
    private

      f : S → S
      f = F e p

      fixedPoint : S → ∃ (λ x → f x ≈ x)
      fixedPoint v = inner (F-inactive e v) (<-wellFounded (d e p (f v) (f (f v))))
        where
        inner : ∀ {x} → WellFormed p x → Acc _<_ (d e p x (f x)) → ∃ (λ x* → f x* ≈ x*)
        inner {x} ≈⊥ (acc x-acc) with F e p x ≟[ p ] x
        ... | yes fx≈ₚx = x , inactiveEq p (F-inactive e x) ≈⊥ fx≈ₚx
        ... | no  fx≉ₚx = inner (F-inactive e x) (x-acc _ (F-strContrOnOrbits e p ≈⊥ fx≉ₚx))

    x* : S
    x* = proj₁ (fixedPoint element)

    Fx*≈x* : F e p x* ≈ x*
    Fx*≈x* = proj₂ (fixedPoint element)

    Fx*≈ₚx* : F e p x* ≈[ p ] x*
    Fx*≈ₚx* = ≈⇒≈ₛ Fx*≈x*
    
    x*-inactive : ∀ {i} → i ∉ₛ p → x* i ≈ᵢ ⊥ i
    x*-inactive {i} i∉p = ≈ᵢ-trans (≈ᵢ-sym (Fx*≈x* i)) (F-inactive e x* i∉p)
    
-----------
-- Boxes --
-----------
-- Definition and properties of the subboxes B

B : Epoch → Subset n → ℕ → IPred Sᵢ _
B e p zero    i xᵢ = Lift ℓ ⊤
B e p (suc k) i xᵢ with i ∈? p
... | yes i∈p = Lift ℓ (dᵢ e p (x* e p i) xᵢ ≤ r[_] e p (suc k))
... | no  i∉p = xᵢ ≈ᵢ ⊥ i

B₀-univ : ∀ x → x ∈ B 0 ⊤ₛ 0
B₀-univ x i = lift tt

B-cong : ∀ {e p k i} → (_∈ᵤ B e p k i) Respects _≈ᵢ_
B-cong {e} {p} {zero}  {i} _   _ = lift tt
B-cong {e} {p} {suc k} {i} x≈y x∈B with i ∈? p
... | yes i∈p = lift (subst (_≤ r[_] e p (suc k)) (dᵢ-cong e p ≈ᵢ-refl x≈y) (lower x∈B))
... | no  i∉p = ≈ᵢ-trans (≈ᵢ-sym x≈y) x∈B

B-null : ∀ {e p k i} → i ∉ₛ p → ⊥ i ∈ᵤ B e p k i
B-null {e} {p} {zero}  {i} _ = lift tt
B-null {e} {p} {suc k} {i} i∉p with i ∈? p
... | yes i∈p = contradiction i∈p i∉p
... | no  _   = ≈ᵢ-refl

B₀-eqᵢ : ∀ {e p} f q {i xᵢ} → xᵢ ∈ᵤ B e p 0 i → xᵢ ∈ᵤ B f q 0 i
B₀-eqᵢ f q x∈B₀ = lift tt

B-finish : ∀ e p → ∃₂ λ k* x* → ∀ {k} → k* ≤ k → (x* ∈ B e p k × (∀ {x} → x ∈ B e p k → x ≈ x*))
B-finish e p = k* e p , x* e p , λ k*≤k → x*∈B[k] k*≤k , x∈B[k]⇒x*≈x k*≤k
  where
  x∈B[k]⇒x*≈x : ∀ {k} → k* e p ≤ k → ∀ {x} → x ∈ B e p k → x ≈ x* e p
  x∈B[k]⇒x*≈x {zero}  k*≤0   {x} x∈B[k] i = dᵢ≡0⇒x≈y e p (n≤0⇒n≡0 (≤-trans (dᵢ≤k* e p (x i) _) k*≤0))
  x∈B[k]⇒x*≈x {suc k} k*≤1+k {x} x∈B[k] i with x∈B[k] i
  ... | xᵢ∈B with i ∈? p
  ...   | no i∉p = ≈ᵢ-trans xᵢ∈B (≈ᵢ-sym (x*-inactive e p i∉p))
  ...   | yes _  = ≈ᵢ-sym (dᵢ≡0⇒x≈y e p (n≤0⇒n≡0 (begin
    dᵢ e p (x* e p i) (x i) ≤⟨ lower xᵢ∈B ⟩
    r[_] e p (suc k)        ≡⟨ k*≤k⇒r[k]≡0 e p k*≤1+k ⟩
    0                       ∎)))

  x*∈B[k] : ∀ {k} → k* e p ≤ k → x* e p ∈ B e p k
  x*∈B[k] {zero}  k*≤k i = lift tt
  x*∈B[k] {suc k} k*≤k i with i ∈? p
  ... | yes _   = lift (subst (_≤ r[_] e p (suc k)) (sym (x≈y⇒dᵢ≡0 e p ≈ᵢ-refl)) z≤n)
  ... | no  i∉p = x*-inactive e p i∉p
  
F-resp-B₀ : ∀ {e p x} → x ∈ B e p 0 → F e p x ∈ B e p 0
F-resp-B₀ x∈B i = x∈B i

∈Bᵢ⇒dᵢ≤r : ∀ {e p b i xᵢ} → xᵢ ∈ᵤ B e p (suc b) i → dₛᵢ e p (x* e p i) xᵢ ≤ r[_] e p (suc b)
∈Bᵢ⇒dᵢ≤r {e} {p} {b} {i} {xᵢ} xᵢ∈B with i ∈? p
... | yes _ = lower xᵢ∈B
... | no  _ = z≤n

∈B⇒d≤r : ∀ {e p b x} → x ∈ B e p b → d e p (x* e p) x ≤ r[_] e p b
∈B⇒d≤r {e} {p} {zero}  {x} x∈B = d≤r[0] e p (x* e p) x
∈B⇒d≤r {e} {p} {suc b} {x} x∈B = max[t]≤x z≤n (λ i → ∈Bᵢ⇒dᵢ≤r (x∈B i))

F-mono-B  : ∀ {e p b x} → WellFormed p x → x ∈ B e p b → F e p x ∈ B e p (suc b)
F-mono-B {e} {p} {b} {x} wf x∈B i with i ∈? p
... | no  i∉p = F-inactive e x i∉p
... | yes i∈p with x ≟[ p ] x* e p
...   | yes x≈ₚx* = lift (begin
  dᵢ e p (x* e p i) (F e p x        i) ≡⟨ dᵢ-cong e p ≈ᵢ-refl (F-cong e p x≈ₚx* i∈p) ⟩
  dᵢ e p (x* e p i) (F e p (x* e p) i) ≡⟨ dᵢ-cong e p ≈ᵢ-refl (Fx*≈ₚx* e p i∈p) ⟩
  dᵢ e p (x* e p i) (x* e p i)         ≡⟨ x≈y⇒dᵢ≡0 e p ≈ᵢ-refl ⟩
  0                                   ≤⟨ z≤n ⟩
  r[_] e p (suc b)                    ∎)
...   | no  x≉ₚx* = lift (v<r[k]⇒v≤r[1+k] e p (begin
  dᵢ e p (x* e p i) (F e p x i) ≤⟨ dᵢ≤d e p (x* e p) (F e p x) i∈p ⟩
  d e p (x* e p)   (F e p x)   <⟨ F-strContrOnFP e p wf (Fx*≈x* e p) x≉ₚx* ⟩
  d e p (x* e p)    x          ≤⟨ ∈B⇒d≤r x∈B ⟩
  r[_] e p b                   ∎))

----------------------
-- ACO construction --
----------------------

aco : ACO 𝓘 ℓ
aco = record
  { B            = B
  ; B₀-eqᵢ       = λ {e p} → B₀-eqᵢ {e} {p}
  ; Bᵢ-cong       = λ {e p k} → B-cong {e} {p} {k}
  ; B-null       = λ {e p k} → B-null {e} {p} {k}
  ; B-finish     = B-finish

  ; F-resp-B₀    = λ {e p x} → F-resp-B₀ {e} {p} {x}
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
-- x∈B[k*]⇒x*≈x : ∀ e p {x} → x ∈ B e p k* → x ≈ x* e p


-- Failure 2
--
-- B e p b i xᵢ with i ∈? p
-- ... | yes i∈p = Lift (dᵢ (x* e p i) xᵢ ≤ r[ suc b ])
-- ... | no  i∉p = xᵢ ≈ᵢ ⊥ i
--
-- causes the following lemma to fail
--
-- B₀-mono : ∀ {e f p q} → e ≤ f → B e p 0 ⊆[ Sᵢ ] B f q 0
