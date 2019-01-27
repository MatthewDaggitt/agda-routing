open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Algebra.FunctionProperties.Core
open import Data.List using (foldr; tabulate)
open import Function using (id; _∘_)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (Rel)
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
open import RoutingLib.Data.Matrix.Relation.Pointwise using (Pointwise; setoid; trans; sym; refl)
import RoutingLib.Data.Matrix.Relation.Equality as MatrixEq
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Algebra

module RoutingLib.lmv34.Gamma_zero.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n
open RawRoutingAlgebra algebra renaming
  (_≈_ to _≡_; ≈-trans to ≡-trans; ≈-sym to ≡-sym; ≈-refl to ≡-refl)
open Gamma_zero algebra A
open Algebra algebra n

infix 2 _≈_
_≈_ : Rel (RoutingMatrix) ℓ
_≈_ = Pointwise _≡_

MS = setoid S n n
≈-trans = trans {b} {ℓ} {Route} {_≡_} ≡-trans
≈-sym = sym {b} {ℓ} {Route} {_≡_} ≡-sym
≈-refl = refl {b} {ℓ} {Route} {_≡_} ≡-refl

infix 20 _^_
_^_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
f ^ zero = id
f ^ (suc n) = f ∘ (f ^ n)

-- Theorem 1
FixedPoint-Γ₀ : ∀ {k} → {Y : RoutingMatrix} →
                (Γ₀ ^ suc k) Y ≈ (Γ₀ ^ k) Y →
                (Γ₀ ^ k) Y ≈ A 〚 (Γ₀ ^ k) Y 〛 M⊕ I
FixedPoint-Γ₀ {k} {Y} p = begin
  (Γ₀ ^ k) Y             ≈⟨ ≈-sym p ⟩
  (Γ₀ ^ suc k) Y          ≈⟨ ≈-refl ⟩
  (A 〚 (Γ₀ ^ k) Y 〛 M⊕ I) ∎
  where open EqReasoning MS

