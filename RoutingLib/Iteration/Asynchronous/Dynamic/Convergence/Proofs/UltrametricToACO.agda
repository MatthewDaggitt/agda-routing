open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (Subset) renaming (_∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
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
import RoutingLib.Function.Metric.FixedPoint as FixedPoints
import RoutingLib.Function.Metric.Construct.SubsetMaxLift as SubsetMaxLift
open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Relation.Binary.PropositionalEquality using (inspect′)
import RoutingLib.Relation.Binary.Indexed.Homogeneous.Construction.FiniteSubset.DecEquality as SubsetEquality

open import RoutingLib.Iteration.Asynchronous.Dynamic using (AsyncIterable)
open import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions using (ACO; UltrametricConditions)
open import RoutingLib.Iteration.Asynchronous.Schedule using (Epoch)

open ≤-Reasoning

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.UltrametricToACO
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

abstract

  dₘₐₓ : ℕ
  dₘₐₓ = proj₁ dᵢ-bounded

  dᵢ≤dₘₐₓ : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ dₘₐₓ
  dᵢ≤dₘₐₓ = proj₂ dᵢ-bounded

module _ (p : Subset n) where

  dₛᵢ-cong : ∀ {i} → dₛᵢ p {i} Preserves₂ _≈ᵢ_ ⟶ _≈ᵢ_ ⟶ _≡_
  dₛᵢ-cong {i} with i ∈? p
  ... | yes i∈p = dᵢ-cong
  ... | no  i∉p = λ _ _ → refl

  dₛ-cong : d p Preserves₂ _≈[ p ]_ ⟶ _≈[ p ]_ ⟶ _≡_
  dₛ-cong = SubsetMaxLift.dˢ-congˢ ≈ᵢ-setoidᵢ dᵢ p dᵢ-cong
  
  d-cong : d p Preserves₂ _≈_ ⟶ _≈_ ⟶ _≡_
  d-cong x≈y u≈v = max-cong refl (λ i → dₛᵢ-cong (x≈y i) (u≈v i))
  
  i∈p⇒dₛᵢ≡dᵢ : ∀ {i} (x y : Sᵢ i) → i ∈ₛ p → dₛᵢ p x y ≡ dᵢ x y 
  i∈p⇒dₛᵢ≡dᵢ {i} x y i∈p with i ∈? p
  ... | yes _   = refl
  ... | no  i∉p = contradiction i∈p i∉p

  dₛᵢ≤dᵢ : ∀ {i} (x y : Sᵢ i) → dₛᵢ p x y ≤ dᵢ x y
  dₛᵢ≤dᵢ {i} x y with i ∈? p
  ... | yes _ = ≤-refl
  ... | no  _ = z≤n

  dᵢ≤d : ∀ x y {i} → i ∈ₛ p → dᵢ (x i) (y i) ≤ d p x y
  dᵢ≤d x y {i} i∈p = x≤max[t] 0 _ (inj₂ (i , ≤-reflexive (sym (i∈p⇒dₛᵢ≡dᵢ (x i) (y i) i∈p))))

  d≤dₘₐₓ : ∀ x y → d p x y ≤ dₘₐₓ
  d≤dₘₐₓ x y = max[t]≤x z≤n (λ i → ≤-trans (dₛᵢ≤dᵢ (x i) (y i)) (dᵢ≤dₘₐₓ (x i) (y i)))
  
---------------------
-- The biggest box --
---------------------

abstract
  
  bᶠ : ℕ
  bᶠ = suc dₘₐₓ

  dᵢ≤bᶠ : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ bᶠ
  dᵢ≤bᶠ x y = begin
    dᵢ x y    ≤⟨ dᵢ≤dₘₐₓ x y ⟩
    dₘₐₓ      ≤⟨ n≤1+n dₘₐₓ ⟩
    bᶠ        ∎

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

  r[bᶠ]≡0 : r[ bᶠ ] ≡ 0
  r[bᶠ]≡0 = m≤n⇒m∸n≡0 (n≤1+n dₘₐₓ)
  
  dᵢ≤r[0] : ∀ {i} (x y : Sᵢ i) → dᵢ x y ≤ r[ 0 ]
  dᵢ≤r[0] x y = dᵢ≤dₘₐₓ x y

  d≤r[0] : ∀ p x y → d p x y ≤ r[ 0 ]
  d≤r[0] p x y = d≤dₘₐₓ p x y

------------------------------
-- Existence of fixed point --
------------------------------

module _ (e : Epoch) (p : Subset n) where

  abstract
    
    private

      f : S → S
      f = F e p

      fixedPoint : S → ∃ (λ x → f x ≈ x)
      fixedPoint v = inner (F-inactive e v) (<-wellFounded (d p (f v) (f (f v))))
        where
        inner : ∀ {x} → WellFormed p x → Acc _<_ (d p x (f x)) → ∃ (λ x* → f x* ≈ x*)
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
-- Definition and properties of the initial box B

B : IPred Sᵢ ℓ
B i xᵢ = Lift ⊤

B-cong : ∀ {i} → (_∈ᵤ B i) Respects _≈ᵢ_
B-cong _ _ = lift tt

B-null : ⊥ ∈ B
B-null _ = lift tt

B-univ : ∀ x → x ∈ B
B-univ _ _ = lift tt

F-resp-B : ∀ {x} → x ∈ B → ∀ {e p} → F e p x ∈ B
F-resp-B x∈B i = x∈B i


-- Definition and properties of the subboxes D

D : Epoch → Subset n → ℕ → IPred Sᵢ _
D e p b i xᵢ with i ∈? p
... | yes i∈p = Lift (dᵢ (x* e p i) xᵢ ≤ r[ b ])
... | no  i∉p = xᵢ ≈ᵢ ⊥ i

D-cong : ∀ {e p b i} → (_∈ᵤ D e p b i) Respects _≈ᵢ_
D-cong {e} {p} {b} {i} x≈y x∈D with i ∈? p
... | yes i∈p = lift (subst (_≤ r[ b ]) (dᵢ-cong ≈ᵢ-refl x≈y) (lower x∈D))
... | no  i∉p = ≈ᵢ-trans (≈ᵢ-sym x≈y) x∈D

D-null : ∀ {e p b i} → i ∉ₛ p → ⊥ i ∈ᵤ D e p b i
D-null {e} {p} {b} {i} i∉p with i ∈? p
... | yes i∈p = contradiction i∈p i∉p
... | no  _   = ≈ᵢ-refl

D-from-B   : ∀ {e p x} → x ∈ B → F e p x ∈ D e p 0
D-from-B {e} {p} {x} _ i with i ∈? p
... | yes i∈p = lift (dᵢ≤r[0] (x* e p i) (F e p x i))
... | no  i∉p = F-inactive e x i∉p

D-finish : ∀ e p → ∃₂ λ bᶠ ξ → (∀ {x} → x ∈ D e p bᶠ → x ≈ ξ)
D-finish e p = bᶠ , x* e p , x∈D[bᶠ]⇒x*≈x
  where
  x∈D[bᶠ]⇒x*≈x : ∀ {x} → x ∈ D e p bᶠ → x ≈ x* e p
  x∈D[bᶠ]⇒x*≈x {x} x∈D[bᶠ] i with inspect′ bᶠ
  ... | (zero     , bᶠ≡0)     = dᵢ≡0⇒x≈y (n≤0⇒n≡0 (subst (dᵢ (x i) (x* e p i) ≤_) bᶠ≡0 (dᵢ≤bᶠ (x i) (x* e p i))))
  ... | (suc bᶠ-1 , bᶠ≡1+bᶠ-1) rewrite bᶠ≡1+bᶠ-1 with x∈D[bᶠ] i
  ...   | xᵢ∈D with i ∈? p
  ...     | no i∉p = ≈ᵢ-trans xᵢ∈D (≈ᵢ-sym (x*-inactive e p i∉p))
  ...     | yes _  = ≈ᵢ-sym (dᵢ≡0⇒x≈y (n≤0⇒n≡0 (begin
    dᵢ (x* e p i) (x i) ≤⟨ lower xᵢ∈D ⟩
    r[ suc bᶠ-1 ]       ≡⟨ cong r[_] (sym bᶠ≡1+bᶠ-1) ⟩
    r[ bᶠ ]             ≡⟨ r[bᶠ]≡0 ⟩
    0                   ∎)))

∈Dᵢ⇒dᵢ≤r : ∀ {e p b i xᵢ} → xᵢ ∈ᵤ D e p (suc b) i → dₛᵢ p (x* e p i) xᵢ ≤ r[ suc b ]
∈Dᵢ⇒dᵢ≤r {e} {p} {b} {i} {xᵢ} xᵢ∈D with i ∈? p
... | yes _ = lower xᵢ∈D
... | no  _ = z≤n

∈D⇒d≤r : ∀ {e p b x} → x ∈ D e p b → d p (x* e p) x ≤ r[ b ]
∈D⇒d≤r {e} {p} {zero}  {x} x∈D = d≤r[0] p (x* e p) x
∈D⇒d≤r {e} {p} {suc b} {x} x∈D = max[t]≤x z≤n (λ i → ∈Dᵢ⇒dᵢ≤r (x∈D i))

F-mono-D  : ∀ {e p b x} → WellFormed p x → x ∈ D e p b → F e p x ∈ D e p (suc b)
F-mono-D {e} {p} {b} {x} wf x∈D i with i ∈? p
... | no  i∉p = F-inactive e x i∉p
... | yes i∈p with x ≟[ p ] x* e p
...   | yes x≈ₚx* = lift (begin
  dᵢ (x* e p i) (F e p x        i) ≡⟨ dᵢ-cong ≈ᵢ-refl (F-cong e p x≈ₚx* i∈p) ⟩
  dᵢ (x* e p i) (F e p (x* e p) i) ≡⟨ dᵢ-cong ≈ᵢ-refl (Fx*≈ₚx* e p i∈p) ⟩
  dᵢ (x* e p i) (x* e p i)         ≡⟨ x≈y⇒dᵢ≡0 ≈ᵢ-refl ⟩
  0                                ≤⟨ z≤n ⟩
  r[ suc b ]                       ∎)
...   | no  x≉ₚx* = lift (v<r[k]⇒v≤r[1+k] (begin
  dᵢ (x* e p i) (F e p x i) ≤⟨ dᵢ≤d p (x* e p) (F e p x) i∈p ⟩
  d p (x* e p)  (F e p x)   <⟨ F-strContrOnFP e p wf (Fx*≈ₚx* e p) x≉ₚx* ⟩
  d p (x* e p)  x           ≤⟨ ∈D⇒d≤r x∈D ⟩
  r[ b ]                    ∎))

----------------------
-- ACO construction --
----------------------

aco : ACO 𝓘 ℓ
aco = record
  { B            = B
  ; B-cong       = B-cong
  ; B-null       = B-null
  ; F-resp-B     = λ {x} → F-resp-B {x}

  ; D            = D
  ; D-cong       = D-cong
  ; D-null       = D-null
  ; D-from-B     = D-from-B
  ; D-finish     = D-finish
  ; F-mono-D     = F-mono-D
  }



-----------------------------------------------------------------
-- Some hard-won knowledge on which box definitions don't work --
-----------------------------------------------------------------

-- Failure 1
--
-- D e p b i xᵢ = dₛᵢ p (x* e p i) xᵢ ≤ r[ b ]
--
-- causes the following lemma to fail when i ∉ p
--
-- x∈D[bᶠ]⇒x*≈x : ∀ e p {x} → x ∈ D e p bᶠ → x ≈ x* e p


-- Failure 2
--
-- D e p b i xᵢ with i ∈? p
-- ... | yes i∈p = Lift (dᵢ (x* e p i) xᵢ ≤ r[ suc b ])
-- ... | no  i∉p = xᵢ ≈ᵢ ⊥ i
--
-- causes the following lemma to fail
--
-- D₀-mono : ∀ {e f p q} → e ≤ f → D e p 0 ⊆[ Sᵢ ] D f q 0
