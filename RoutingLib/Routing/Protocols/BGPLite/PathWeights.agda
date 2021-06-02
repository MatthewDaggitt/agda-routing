--------------------------------------------------------------------------------
-- Agda routing library
--
-- The underlying data contained in each path-weight in the BGPLite algebra.
-- Each path-weight is either invalid or consists of a level, a set of
-- communities and the path along which it was generated.
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Nat.Properties hiding (≡-isDecEquivalence)
import Data.Fin.Properties as Fin
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.Fin.Induction using (_>_)

open import RoutingLib.Routing.Basics.Path.Uncertified
open import RoutingLib.Routing.Basics.Path.Uncertified.Properties

open import RoutingLib.Routing.Protocols.BGPLite.LocalPref
open import RoutingLib.Routing.Protocols.BGPLite.Communities

module RoutingLib.Routing.Protocols.BGPLite.PathWeights where

------------------------------------------------------------------------
-- Types

data PathWeight : Set where
  invalid : PathWeight
  valid   : (l : LocalPref) → (cs : Communities) → (p : Path) → PathWeight

------------------------------------------------------------------------
-- Equality over path-weights

_≟ᵣ_ : Decidable {A = PathWeight} _≡_
invalid      ≟ᵣ invalid      = yes refl
invalid      ≟ᵣ valid l cs p = no λ()
valid l cs p ≟ᵣ invalid      = no λ()
valid l cs p ≟ᵣ valid k ds q with l ≟ˡᵖ k | cs ≟ᶜˢ ds | p ≟ₚ q
... | no  l≢k  | _         | _        = no λ {refl → l≢k   refl}
... | yes _    | no  cs≉ds | _        = no λ {refl → cs≉ds refl}
... | yes _    | yes _     | no  p≉q  = no λ {refl → p≉q   refl}
... | yes refl | yes refl  | yes refl = yes refl

≡ᵣ-isEquivalence : IsEquivalence {A = PathWeight} _≡_
≡ᵣ-isEquivalence = isEquivalence

≡ᵣ-isDecEquivalence : IsDecEquivalence {A = PathWeight} _≡_
≡ᵣ-isDecEquivalence = record
  { isEquivalence = ≡ᵣ-isEquivalence
  ; _≟_           = _≟ᵣ_
  }

------------------------------------------------------------------------
-- A total ordering over path-weights

infix 4 _≤ᵣ_ _≰ᵣ_

data _≤ᵣ_ : Rel PathWeight ℓ₀ where
  invalid : ∀ {r} → r ≤ᵣ invalid
  pref>   : ∀ {k l cs ds p q} → k >ˡᵖ l → valid k cs p ≤ᵣ valid l ds q
  length< : ∀ {k l cs ds p q} → k ≡ l → length p < length q → valid k cs p ≤ᵣ valid l ds q
  plex<   : ∀ {k l cs ds p q} → k ≡ l → length p ≡ length q → p <ₗₑₓ q → valid k cs p ≤ᵣ valid l ds q
  comm≤   : ∀ {k l cs ds p q} → k ≡ l → p ≈ₚ q → cs ≤ᶜˢ ds → valid k cs p ≤ᵣ valid l ds q

_≰ᵣ_ : Rel PathWeight ℓ₀
r ≰ᵣ s = ¬ (r ≤ᵣ s)

≤ᵣ-total : Total _≤ᵣ_
≤ᵣ-total invalid s = inj₂ invalid
≤ᵣ-total r invalid = inj₁ invalid
≤ᵣ-total (valid l cs p) (valid k ds q) with <ˡᵖ-compare l k
... | tri< l<k _ _ = inj₂ (pref> l<k)
... | tri> _ _ k<l = inj₁ (pref> k<l)
... | tri≈ _ l≡k _ with <-cmp (length p) (length q)
...   | tri< |p|<|q| _ _ = inj₁ (length< l≡k |p|<|q|)
...   | tri> _ _ |q|<|p| = inj₂ (length< (sym l≡k) |q|<|p|)
...   | tri≈ _ |p|≡|q| _ with <ₗₑₓ-cmp p q
...     | tri< p<q _ _ = inj₁ (plex< l≡k |p|≡|q| p<q)
...     | tri> _ _ q<p = inj₂ (plex< (sym l≡k) (sym |p|≡|q|) q<p)
...     | tri≈ _ p≈q _ with ≤ᶜˢ-total cs ds
...       | inj₁ cs≤ds = inj₁ (comm≤ l≡k p≈q cs≤ds)
...       | inj₂ ds≤cs = inj₂ (comm≤ (sym l≡k) (sym p≈q) ds≤cs)

≤ᵣ-refl : Reflexive _≤ᵣ_
≤ᵣ-refl {invalid}      = invalid
≤ᵣ-refl {valid l cs p} = comm≤ refl refl ≤ᶜˢ-refl

≤ᵣ-reflexive : _≡_ ⇒ _≤ᵣ_
≤ᵣ-reflexive refl = ≤ᵣ-refl

≤ᵣ-trans : Transitive _≤ᵣ_
≤ᵣ-trans invalid                    invalid                    = invalid
≤ᵣ-trans (pref>  l<k)               invalid                    = invalid
≤ᵣ-trans (pref>  l<k)               (pref>  k<m)               = pref> (<ˡᵖ-trans k<m l<k)
≤ᵣ-trans (pref>  l<k)               (length< refl |q|<|r|)     = pref> l<k
≤ᵣ-trans (pref>  l<k)               (plex<   refl |q|≡|r| q<r) = pref> l<k
≤ᵣ-trans (pref>  l<k)               (comm≤   refl q≈r ds≤es)   = pref> l<k
≤ᵣ-trans (length< refl |p|<|q|)     invalid                    = invalid
≤ᵣ-trans (length< refl |p|<|q|)     (pref>  k<m)               = pref> k<m
≤ᵣ-trans (length< refl |p|<|q|)     (length< k≡m |q|<|r|)      = length< k≡m (<-trans |p|<|q| |q|<|r|)
≤ᵣ-trans (length< refl |p|<|q|)     (plex<   k≡m |q|≡|r| q<r)  = length< k≡m (subst (_ <_) |q|≡|r| |p|<|q|)
≤ᵣ-trans (length< refl |p|<|q|)     (comm≤   k≡m refl ds≤es)   = length< k≡m |p|<|q|
≤ᵣ-trans (plex<   refl |p|≡|q| p<q) invalid                    = invalid
≤ᵣ-trans (plex<   refl |p|≡|q| p<q) (pref>  k<m)               = pref> k<m
≤ᵣ-trans (plex<   refl |p|≡|q| p<q) (length< k≡m |q|<|r|)      = length< k≡m (subst (_< _) (sym |p|≡|q|) |q|<|r|)
≤ᵣ-trans (plex<   refl |p|≡|q| p<q) (plex<   k≡m |q|≡|r| q<r)  = plex< k≡m (trans |p|≡|q| |q|≡|r|) (<ₗₑₓ-trans p<q q<r)
≤ᵣ-trans (plex<   refl |p|≡|q| p<q) (comm≤   k≡m refl ds≤es)   = plex< k≡m |p|≡|q| p<q
≤ᵣ-trans (comm≤   refl p≈q cs≤ds)   invalid                    = invalid
≤ᵣ-trans (comm≤   refl refl cs≤ds)  (pref>  k<m)               = pref> k<m
≤ᵣ-trans (comm≤   refl refl cs≤ds)  (length< k≡m |q|<|r|)      = length< k≡m |q|<|r|
≤ᵣ-trans (comm≤   refl refl cs≤ds)  (plex<   k≡m |q|≡|r| q<r)  = plex< k≡m |q|≡|r| q<r
≤ᵣ-trans (comm≤   refl refl cs≤ds)  (comm≤   k≡m q≈r ds≤es)    = comm≤ k≡m q≈r (≤ᶜˢ-trans cs≤ds ds≤es)

≤ᵣ-antisym : Antisymmetric _≡_ _≤ᵣ_
≤ᵣ-antisym invalid                 invalid               = refl
≤ᵣ-antisym (pref> k<l)             (pref>  l<k)          = contradiction k<l (<ˡᵖ-asym l<k)
≤ᵣ-antisym (pref> k<l)             (length< refl _)      = contradiction k<l (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (pref> k<l)             (plex<   refl _ _)    = contradiction k<l (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (pref> k<l)             (comm≤   refl _ _)    = contradiction k<l (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (length< refl _)        (pref>  l<k)          = contradiction l<k (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (length< _ |p|<|q|)     (length< _ |q|<|p|)   = contradiction |p|<|q| (<-asym |q|<|p|)
≤ᵣ-antisym (length< _ |p|<|q|)     (plex<   _ |q|≡|p| _) = contradiction |p|<|q| (<-irrefl (sym |q|≡|p|))
≤ᵣ-antisym (length< _ |p|<|q|)     (comm≤   _ refl _)    = contradiction |p|<|q| (<-irrefl refl)
≤ᵣ-antisym (plex< refl _ _)        (pref> l<k)           = contradiction l<k (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (plex< _ |p|≡|q| _)     (length< _ |q|<|p|)   = contradiction |q|<|p| (<-irrefl (sym |p|≡|q|))
≤ᵣ-antisym (plex< _ _ p<q)         (plex< _ _ q<p)       = contradiction p<q (<ₗₑₓ-asym q<p)
≤ᵣ-antisym (plex< _ _ p<q)         (comm≤ _ refl _)      = contradiction p<q (<ₗₑₓ-irrefl refl)
≤ᵣ-antisym (comm≤ refl _ _)        (pref> l<k)           = contradiction l<k (<ˡᵖ-irrefl refl)
≤ᵣ-antisym (comm≤ _ refl _)        (length< _ |q|<|p|)   = contradiction |q|<|p| (<-irrefl refl)
≤ᵣ-antisym (comm≤ _ refl _)        (plex< _ _ q<p)       = contradiction q<p (<ₗₑₓ-irrefl refl)
≤ᵣ-antisym (comm≤ refl refl cs≤ds) (comm≤ _ _ ds≤cs)     = cong (λ v → valid _ v _) (≤ᶜˢ-antisym cs≤ds ds≤cs)

≤ᵣ-minimum : Minimum _≤ᵣ_ (valid 2⁸-1 ∅ [])
≤ᵣ-minimum invalid        = invalid
≤ᵣ-minimum (valid l cs p) with <ˡᵖ-compare l 2⁸-1
... | tri< l<2⁸-1 _ _ = pref> l<2⁸-1
... | tri> _ _ 2⁸-1<l = contradiction 2⁸-1<l (≤⇒≯ (≤ˡᵖ-max l))
... | tri≈ _ refl _ with <-cmp 0 (length p)
...   | tri< 0<|p| _ _ = length< refl 0<|p|
...   | tri> _ _ ()
...   | tri≈ _ 0≡|p| _ with <ₗₑₓ-cmp [] p
...     | tri< []<p _ _ = plex< refl 0≡|p| []<p
...     | tri> _ _ p<[] = contradiction p<[] p≮ₗₑₓ[]
...     | tri≈ _ refl _ with ≤ᶜˢ-total ∅ cs
...       | inj₁ ∅≤cs = comm≤ refl refl ∅≤cs
...       | inj₂ cs≤∅ = ≤ᵣ-reflexive (cong (λ v → valid _ v _) (≤ᶜˢ-antisym (≤ᶜˢ-minimum cs) cs≤∅))

≤ᵣ-maximum : Maximum _≤ᵣ_ invalid
≤ᵣ-maximum x = invalid

≤ᵣ-respˡ-≈ᵣ : ∀ {x y z} → y ≡ z → x ≤ᵣ y → x ≤ᵣ z
≤ᵣ-respˡ-≈ᵣ refl x≤y = x≤y

≤ᵣ-respʳ-≈ᵣ : ∀ {x y z} → y ≡ z → y ≤ᵣ x → z ≤ᵣ x
≤ᵣ-respʳ-≈ᵣ refl y≤x = y≤x

≤ᵣ-resp-≈ᵣ : _≤ᵣ_ Respects₂ _≡_
≤ᵣ-resp-≈ᵣ = ≤ᵣ-respˡ-≈ᵣ , ≤ᵣ-respʳ-≈ᵣ

≤ᵣ-isPartialOrder : IsPartialOrder _≡_ _≤ᵣ_
≤ᵣ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = ≡ᵣ-isEquivalence
    ; reflexive = ≤ᵣ-reflexive
    ; trans = ≤ᵣ-trans
    }
  ; antisym = ≤ᵣ-antisym
  }

≤ᵣ-poset : Poset _ _ _
≤ᵣ-poset = record
  { isPartialOrder = ≤ᵣ-isPartialOrder
  }

≤ᵣ-totalOrder : TotalOrder _ _ _
≤ᵣ-totalOrder = record
  { isTotalOrder = record
    { isPartialOrder = ≤ᵣ-isPartialOrder
    ; total = ≤ᵣ-total
    }
  }

≤ᵣ-reject : ∀ {k l p q cs ds} → l ≥ˡᵖ k → length p < length q → valid k ds q ≰ᵣ valid l cs p
≤ᵣ-reject l≤k |p|<|q| (pref> k<l)         = <⇒≱ k<l l≤k
≤ᵣ-reject l≤k |p|<|q| (length< _ |q|<|p|) = <-asym |p|<|q| |q|<|p|
≤ᵣ-reject l≤k |p|<|q| (plex< _ |q|≡|p| _) = <-irrefl (sym |q|≡|p|) |p|<|q|
≤ᵣ-reject l≤k |p|<|q| (comm≤ _ refl _)    = <-irrefl refl |p|<|q|
