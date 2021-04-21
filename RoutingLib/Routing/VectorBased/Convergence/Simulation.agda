--------------------------------------------------------------------------------
-- Agda routing library
--
-- The proof that if algebra A simulates algebra B then if the vector-based
-- protocol based on A converges then so does the vector-based protocol based
-- on algebra B. This is based on a reduction to the simulation results for
-- general dynamic asynchronous iterations found in `RoutingLib.Iteration`.
--------------------------------------------------------------------------------

open import Data.Fin using (Fin; _≟_)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List using (foldr; tabulate; map)
open import Data.List.Properties using (tabulate-cong; map-tabulate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (tabulate⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Equality.Setoid using (foldr⁺)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Nat using (ℕ; _+_)
open import Function using (_∘_; _∘₂′_)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (REL)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import RoutingLib.Routing.Prelude using (Network; RoutingMatrix; AdjacencyMatrix; I)
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.List.Properties using (foldr-map-commute-gen₂)

open import RoutingLib.Routing.VectorBased.Convergence.Definitions
open import RoutingLib.Iteration.Asynchronous.Dynamic as Async using (Epoch)
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence as Async
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Simulation
import RoutingLib.Routing.Algebra.Comparable as Comparable
import RoutingLib.Routing.VectorBased.Asynchronous as AsyncBellmanFord
import RoutingLib.Routing.VectorBased.Synchronous as SyncBellmanFord

module RoutingLib.Routing.VectorBased.Convergence.Simulation
  {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂}
  {A : RawRoutingAlgebra a₁ b₁ ℓ₁}
  {B : RawRoutingAlgebra a₂ b₂ ℓ₂}
  (A⇉B : A Simulates B)
  where

open RawRoutingAlgebra hiding (_≟_)
open RawRoutingAlgebra A using ()
  renaming (_≈_ to _≈ᵃ_; _⊕_ to _⊕ᵃ_; _▷_ to _▷ᵃ_; 0# to 0#ᵃ; ∞# to ∞ᵃ)
open RawRoutingAlgebra B using ()
  renaming (_≈_ to _≈ᵇ_; _⊕_ to _⊕ᵇ_; _▷_ to _▷ᵇ_; 0# to 0#ᵇ; ∞# to ∞ᵇ; ≈-refl to ≈ᵇ-refl)
open _Simulates_ A⇉B

open import Data.List.Relation.Binary.Equality.Setoid (S B) as ≋ using (≋-reflexive)

private
  variable
    n : ℕ
    e : Epoch
    p : Subset n
    i : Fin n

--------------------------------------------------------------------------------
-- Proof

from-injective : ∀ {x y} → from x ≈ᵃ from y → x ≈ᵇ y
from-injective {x} {y} f[x]≈f[y] = begin
  x           ≈˘⟨ to-from x ⟩
  to (from x) ≈⟨  to-cong f[x]≈f[y] ⟩
  to (from y) ≈⟨  to-from y ⟩
  y           ∎
  where open SetoidReasoning (S B)

toₘ : RoutingMatrix A n → RoutingMatrix B n
toₘ X i j = to (X i j)

fromₘ : RoutingMatrix B n → RoutingMatrix A n
fromₘ X i j = from (X i j)

toₐ : AdjacencyMatrix A n → AdjacencyMatrix B n
toₐ N i j = toₛ (N i j)

fromₐ : AdjacencyMatrix B n → AdjacencyMatrix A n
fromₐ N i j = fromₛ (N i j)

module _ {n : ℕ} where

  open RoutingLib.Routing.Prelude A n using () renaming (I to Iᵃ)
  open RoutingLib.Routing.Prelude B n using () renaming (I to Iᵇ)

  toIᵃ≈Iᵇ : ∀ i j → to (Iᵃ i j) ≈ᵇ Iᵇ i j
  toIᵃ≈Iᵇ i j with j ≟ i
  ... | yes _ = to-0#
  ... | no  _ = to-∞

module _ (Aᵃ : AdjacencyMatrix A n) (Aᵇ : AdjacencyMatrix B n)
         (Aᵃ≡Aᵇ : ∀ i j → toₛ (Aᵃ i j) ≡ Aᵇ i j)
         where
  
  open SyncBellmanFord A Aᵃ using () renaming (σ to σᴬ; F to Fᵃ; I to Iᵃ)
  open SyncBellmanFord B Aᵇ using () renaming (σ to σᴮ; F to Fᵇ; I to Iᵇ; F-cong to Fᵇ-cong)
  open Comparable A
  
  All-≎-tabulate : ∀ (X : RoutingMatrix A n) j → All (_≎ Iᵃ i j) (tabulate (λ k → Aᵃ i k ▷ᵃ X k j))
  All-≎-tabulate {i} X j with j ≟ i
  ... | yes _ = tabulate⁺ (λ k → e0# (Aᵃ i k) (X k j) (≈-refl A) (≈-refl A))
  ... | no  _ = tabulate⁺ (λ k → e∞# (Aᵃ i k) (X k j) (≈-refl A) (≈-refl A))
  
  AllPairs-≎-tabulate : ∀ (X : RoutingMatrix A n) j → AllPairs _≎_ (tabulate (λ k → Aᵃ i k ▷ᵃ X k j))
  AllPairs-≎-tabulate {i} X j = AllPairs.tabulate⁺ (λ i≢j → ee# (Aᵃ i _) (Aᵃ i _) (X _ j) (X _ j) i≢j (≈-refl A) (≈-refl A))
  
  F-simulate : ∀ (X : RoutingMatrix A n) j → to (Fᵃ X i j) ≈ᵇ Fᵇ (toₘ X) i j
  F-simulate {i} X j = begin
      to (Fᵃ X i j)
    ≡⟨⟩
      to (foldr _⊕ᵃ_ (Iᵃ i j) (tabulate (λ k → Aᵃ i k ▷ᵃ X k j)))
    ≈⟨ ≈-sym B (foldr-map-commute-gen₂ (S B) (⊕-cong B) ⊕-pres-≎ to-⊕ (All-≎-tabulate X j) (AllPairs-≎-tabulate X j)) ⟩
      foldr _⊕ᵇ_ (to (Iᵃ i j)) (map to (tabulate λ k → Aᵃ i k ▷ᵃ X k j))
    ≈⟨ foldr⁺ (S B) (⊕-cong B) (toIᵃ≈Iᵇ i j) (≋-reflexive (map-tabulate (λ k → Aᵃ i k ▷ᵃ X k j) to)) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → to (Aᵃ i k ▷ᵃ X k j)))
    ≈⟨ foldr⁺ (S B) (⊕-cong B) (≈-refl B) (≋.tabulate⁺ (λ k → to-▷ (Aᵃ i k) (X k j)) ) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → toₛ (Aᵃ i k) ▷ᵇ to (X k j)))
    ≡⟨ cong (foldr _⊕ᵇ_ (Iᵇ i j)) (tabulate-cong {n = n} λ k → cong (_▷ᵇ _) (Aᵃ≡Aᵇ i k)) ⟩
      foldr _⊕ᵇ_ (Iᵇ i j) (tabulate (λ k → Aᵇ i k ▷ᵇ to (X k j)))
    ≡⟨⟩
      Fᵇ (λ k l → to (X k l)) i j
    ∎ where open SetoidReasoning (S B)

  σ-simulate : ∀ t X i j → to (σᴬ t X i j) ≈ᵇ σᴮ t (toₘ X) i j
  σ-simulate ℕ.zero    X i j = ≈ᵇ-refl
  σ-simulate (ℕ.suc t) X i j = begin
    to (σᴬ (ℕ.suc t) X i j)  ≡⟨⟩
    to (Fᵃ (σᴬ t X) i j)     ≈⟨ F-simulate (σᴬ t X) j ⟩
    Fᵇ (toₘ (σᴬ t X)) i j    ≈⟨ Fᵇ-cong (σ-simulate t X) i j ⟩
    Fᵇ (σᴮ t (toₘ X)) i j    ≡⟨⟩
    σᴮ (ℕ.suc t) (toₘ X) i j ∎
    where open SetoidReasoning (S B)
    
module _ (Nᵇ : Network B n) where

  Nᵃ : Network A n
  Nᵃ e = fromₐ (Nᵇ e)

  open AsyncBellmanFord A Nᵃ using (RoutingMatrix) renaming (F′ to Fᵃ; F∥ to F∥ᵃ; I to Iᵃ; Aₜ to Aᵃ)
  open AsyncBellmanFord B Nᵇ using () renaming (F′ to Fᵇ; F∥ to F∥ᵇ; I to Iᵇ; Aₜ to Aᵇ; F-cong to Fᵇ-cong)

  toA : ∀ i j → toₛ (Aᵃ e p i j) ≡ Aᵇ e p i j
  toA {e} {p} i j with i ∈? p | j ∈? p
  ... | no  _ | _     = to-f∞
  ... | yes _ | no  _ = to-f∞
  ... | yes _ | yes _ = toₛ-fromₛ (Nᵇ e i j)

  to-F′ : ∀ {e p} X j → to (Fᵃ e p X i j) ≈ᵇ Fᵇ e p (λ k l → to (X k l)) i j
  to-F′ {e = e} {p} = F-simulate (Aᵃ e p) (Aᵇ e p) toA 
  
  F∥ᵃ⇉F∥ᵇ : F∥ᵃ Async.Simulates F∥ᵇ
  F∥ᵃ⇉F∥ᵇ = record
    { toᵢ       = to ∘_
    ; fromᵢ     = from ∘_
    ; toᵢ-⊥     = λ {i} → toIᵃ≈Iᵇ i
    ; toᵢ-cong  = to-cong ∘_
    ; toᵢ-F     = to-F′
    ; toᵢ-fromᵢ = to-from ∘_
    }

open AsyncBellmanFord using (F∥)
open SyncBellmanFord using (σ; σ-cong; ℝ𝕄ₛ)

convergent : Convergent A → Convergent B
convergent convergent Nᵇ = Async.simulate (F∥ᵃ⇉F∥ᵇ Nᵇ) (convergent (fromₐ ∘ Nᵇ))

syncConvergesIn : ∀ f → SynchronouslyConvergesIn A f → SynchronouslyConvergesIn B f 
syncConvergesIn f convergesIn {n} Aᴮ X t = begin
  σ B Aᴮ (f n + t)                     X   ≈˘⟨ σ-cong B Aᴮ (f n + t) (λ i j → to-from (X i j)) ⟩
  σ B Aᴮ (f n + t)         (toₘ (fromₘ X)) ≈˘⟨ σ-simulate (fromₐ Aᴮ) Aᴮ (λ i j → toₛ-fromₛ (Aᴮ i j)) (f n + t) (fromₘ X) ⟩ 
  toₘ (σ A (fromₐ Aᴮ) (f n + t) (fromₘ X)) ≈⟨ (λ i j → to-cong (convergesIn (fromₐ Aᴮ) (fromₘ X) t i j)) ⟩
  toₘ (σ A (fromₐ Aᴮ) (f n)     (fromₘ X)) ≈⟨ σ-simulate (fromₐ Aᴮ) Aᴮ (λ i j → toₛ-fromₛ (Aᴮ i j)) (f n) (fromₘ X) ⟩
  σ B Aᴮ (f n)             (toₘ (fromₘ X)) ≈⟨ σ-cong B Aᴮ (f n) (λ i j → to-from (X i j)) ⟩
  σ B Aᴮ (f n)                         X   ∎
  where open SetoidReasoning (ℝ𝕄ₛ B Aᴮ)
