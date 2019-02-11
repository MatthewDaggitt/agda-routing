open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties
  using (_<?_; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
  renaming (<-cmp to compare)
open import Data.List using (List)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; inspect; [_]; module ≡-Reasoning)
open import Relation.Binary using (Minimum; Maximum)
open import Level using () renaming (zero to ℓ₀; suc to lsuc)

import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder as NaturalChoice

open import RoutingLib.Data.Path.Uncertified using (inflate; deflate; length)
open import RoutingLib.Data.Path.Uncertified.Properties
  using (∈-deflate⁻; ⇿-deflate⁺; deflate-inflate; deflate-skip; ij⇿p⇒i≢j; _≤ₗₑₓ?_; ≤ₗₑₓ-total; ≤ₗₑₓ-antisym)
open import RoutingLib.Data.Path.UncertifiedI hiding (length)
open import RoutingLib.Data.Path.UncertifiedI.Properties

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Comparable as Comparable

open import RoutingLib.Routing.Protocols.BGPLite
open import RoutingLib.Routing.Protocols.BGPLite.Components.Route
open import RoutingLib.Routing.Protocols.BGPLite.Components.Policy
  using (Policy; apply; reject; apply-result)
open import RoutingLib.Routing.Protocols.BGPLite.Components.Communities

module RoutingLib.Routing.Protocols.BGPLite.Properties where

open module Choice = NaturalChoice ≤ᵣ-totalOrder

---------------------
-- Routing algebra --
---------------------


{-
⊕-sel : Selective _≡_ _⊕_
⊕-sel invalid        invalid        = inj₁ refl
⊕-sel invalid        (valid m ds q) = inj₂ refl
⊕-sel (valid l cs p) invalid        = inj₁ refl
⊕-sel (valid l cs p) (valid m ds q) with compare l m
... | tri< _ _ _ = inj₁ refl
... | tri> _ _ _ = inj₂ refl
... | tri≈ _ _ _ with compare (length p) (length q)
...   | tri< _ _ _  = inj₁ refl
...   | tri> _ _ _  = inj₂ refl
...   | tri≈ _ _ _  with p ≤ₗₑₓ? q
...     | yes p≤q = inj₁ refl
...     | no  q≤p = inj₂ refl

⊕-comm : ComparablyCommutative _≡_ _⊕_
⊕-comm {invalid}      {invalid}      x≎y = refl
⊕-comm {invalid}      {valid l cs p} x≎y = refl
⊕-comm {valid l cs p} {invalid}      x≎y = refl
⊕-comm {valid l cs p} {valid k ds q} x≎y with compare l k | compare k l
... | tri< _   _ _ | tri> _ _ _   = refl
... | tri< l<k _ _ | tri≈ _ _ l≮k = contradiction l<k l≮k
... | tri< l<k _ _ | tri< _ _ l≮k = contradiction l<k l≮k
... | tri> _   _ _ | tri< _ _ _   = refl
... | tri> _ _ k<l | tri≈ k≮l _ _ = contradiction k<l k≮l
... | tri> _ _ k<l | tri> k≮l _ _ = contradiction k<l k≮l
... | tri≈ _ l≡k _ | tri< _ k≢l _ = contradiction (sym l≡k) k≢l
... | tri≈ _ l≡k _ | tri> _ k≢l _ = contradiction (sym l≡k) k≢l
... | tri≈ _ l≡k _ | tri≈ _ _ _   with compare (lengthᵥ p) (lengthᵥ q) | compare (lengthᵥ q) (lengthᵥ p)
...   | tri< _ _ _       | tri> _ _ _       = refl
...   | tri< |p|<|q| _ _ | tri≈ _ _ |p|≮|q| = contradiction |p|<|q| |p|≮|q|
...   | tri< |p|<|q| _ _ | tri< _ _ |p|≮|q| = contradiction |p|<|q| |p|≮|q|
...   | tri> _ _ _       | tri< _ _ _       = refl
...   | tri> _ _ |q|<|p| | tri≈ |q|≮|p| _ _ = contradiction |q|<|p| |q|≮|p|
...   | tri> _ _ |q|<|p| | tri> |q|≮|p| _ _ = contradiction |q|<|p| |q|≮|p|
...   | tri≈ _ |p|≡|q| _ | tri< _ |q|≢|p| _ = contradiction (sym |p|≡|q|) |q|≢|p|
...   | tri≈ _ |p|≡|q| _ | tri> _ |q|≢|p| _ = contradiction (sym |p|≡|q|) |q|≢|p|
...   | tri≈ _ |p|≡|q| _ | tri≈ _ _ _       with p ≤ₗₑₓ? q | q ≤ₗₑₓ? p
...     | yes p≤q | yes q≤p = contradiction (≤ₗₑₓ-antisym p≤q q≤p) (≎⇒path≢ l≡k x≎y)
...     | yes p≤q | no  q≤p = refl
...     | no  p≰q | yes q≤p = refl
...     | no  p≰q | no  q≰p with ≤ₗₑₓ-total p q
...       | inj₁ p≤q = contradiction p≤q p≰q
...       | inj₂ q≤p = contradiction q≤p q≰p
-}

⊕-identityʳ  : RightIdentity _≡_ invalid _⊕_
⊕-identityʳ invalid        = refl
⊕-identityʳ (valid l cs p) = refl

{-
⊕-zeroʳ : RightZero _≡_ 0# _⊕_
⊕-zeroʳ invalid = refl
⊕-zeroʳ (valid l cs p) with compare l 0
... | tri< l<0 _ _ = contradiction l<0 λ()
... | tri> _   _ _ = refl
... | tri≈ _   _ _ with compare (length p) 0
...   | tri< |p|<0 _ _ = contradiction |p|<0 λ()
...   | tri> _     _ _ = refl
...   | tri≈ _     _ _ with p ≤ₗₑₓ? []
...     | yes []≤p = {!!}
...     | no  _    = refl
-}

--------------------------------------------------------------------------------
-- The algebra always converges (proved via a simulation with an equivalent but
-- better behaved routing algebra).

open import RoutingLib.Routing.Protocols.BGPLite.Simulation
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence

δ-alwaysConvergent : AlwaysConvergent A
δ-alwaysConvergent = simulate Aₐₗₜ-simulates-A Aₐₗₜ-alwaysConvergent
