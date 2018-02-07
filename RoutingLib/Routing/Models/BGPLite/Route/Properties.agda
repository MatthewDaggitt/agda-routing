open import Data.Nat using (ℕ; _≟_; _<_)
open import Data.Nat.Properties using (<-cmp; <-trans; <-asym; <-irrefl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Relation.Binary.Lattice using (Minimum; Maximum)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Graph.SimplePath2.NonEmpty
  using ([]; length; <ₗₑₓ-cmp; <ₗₑₓ-trans; <ₗₑₓ-resp-≈; <ₗₑₓ-asym; <ₗₑₓ-irrefl;
         <ₗₑₓ-minimum; <ₗₑₓ-respˡ-≈; <ₗₑₓ-respʳ-≈)
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties
  renaming (≈-refl to ≈ₚ-refl; ≈-trans to ≈ₚ-trans; ≈-sym to ≈ₚ-sym; _≟_ to _≟ₚ_)
open import RoutingLib.Routing.Models.BGPLite.Communities
import RoutingLib.Routing.Models.BGPLite.Route as Routes

module RoutingLib.Routing.Models.BGPLite.Route.Properties (n : ℕ) where

  open Routes n
  
  --------------
  -- Equality --
  --------------

  ≈ᵣ-refl : Reflexive _≈ᵣ_
  ≈ᵣ-refl {invalid}      = invalidEq
  ≈ᵣ-refl {route l cs p} = routeEq refl ≈ᶜˢ-refl ≈ₚ-refl

  ≈ᵣ-reflexive : _≡_ ⇒ _≈ᵣ_
  ≈ᵣ-reflexive refl = ≈ᵣ-refl
  
  ≈ᵣ-sym : Symmetric _≈ᵣ_
  ≈ᵣ-sym invalidEq               = invalidEq
  ≈ᵣ-sym (routeEq k≡l cs≈ds p≈q) =
    routeEq (sym k≡l) (≈ᶜˢ-sym cs≈ds) (≈ₚ-sym p≈q)

  ≈ᵣ-trans : Transitive _≈ᵣ_
  ≈ᵣ-trans invalidEq invalidEq = invalidEq
  ≈ᵣ-trans (routeEq refl cs≈ds p≈q) (routeEq refl ds≈es q≈r) =
    routeEq refl (≈ᶜˢ-trans cs≈ds ds≈es) (≈ₚ-trans p≈q q≈r)

  _≟ᵣ_ : Decidable _≈ᵣ_
  invalid      ≟ᵣ invalid      = yes invalidEq
  invalid      ≟ᵣ route l cs p = no λ()
  route l cs p ≟ᵣ invalid      = no λ()
  route l cs p ≟ᵣ route k ds q with l ≟ k | cs ≟ᶜˢ ds | p ≟ₚ q
  ... | no  l≢k | _         | _       = no λ {(routeEq l≡k   _ _) → l≢k   l≡k}
  ... | _       | no  cs≉ds | _       = no λ {(routeEq _ cs≈ds _) → cs≉ds cs≈ds}
  ... | _       | _         | no  p≉q = no λ {(routeEq _ _   p≈q) → p≉q   p≈q}
  ... | yes l≡k | yes cs≈ds | yes p≈q = yes (routeEq l≡k cs≈ds p≈q)

  ≈ᵣ-isEquivalence : IsEquivalence _≈ᵣ_
  ≈ᵣ-isEquivalence = record
    { refl  = ≈ᵣ-refl
    ; sym   = ≈ᵣ-sym
    ; trans = ≈ᵣ-trans
    }
  
  ≈ᵣ-isDecEquivalence : IsDecEquivalence _≈ᵣ_
  ≈ᵣ-isDecEquivalence = record
    { isEquivalence = ≈ᵣ-isEquivalence
    ; _≟_           = _≟ᵣ_
    }


  ------------
  -- Orders --
  ------------

  ≤ᵣ-total : Total _≤ᵣ_
  ≤ᵣ-total invalid s = inj₂ invalid
  ≤ᵣ-total r invalid = inj₁ invalid
  ≤ᵣ-total (route l cs p) (route k ds q) with <-cmp l k
  ... | tri< l<k _ _ = inj₁ (level< l<k)
  ... | tri> _ _ k<l = inj₂ (level< k<l)
  ... | tri≈ _ l≡k _ with <-cmp (length p) (length q)
  ...   | tri< |p|<|q| _ _ = inj₁ (length< l≡k |p|<|q|)
  ...   | tri> _ _ |q|<|p| = inj₂ (length< (sym l≡k) |q|<|p|)
  ...   | tri≈ _ |p|≡|q| _ with <ₗₑₓ-cmp p q
  ...     | tri< p<q _ _ = inj₁ (plex< l≡k |p|≡|q| p<q)
  ...     | tri> _ _ q<p = inj₂ (plex< (sym l≡k) (sym |p|≡|q|) q<p)
  ...     | tri≈ _ p≈q _ with ≤ᶜˢ-total cs ds
  ...       | inj₁ cs≤ds = inj₁ (comm≤ l≡k p≈q cs≤ds)
  ...       | inj₂ ds≤cs = inj₂ (comm≤ (sym l≡k) (≈ₚ-sym p≈q) ds≤cs)
  
  ≤ᵣ-refl : Reflexive _≤ᵣ_
  ≤ᵣ-refl {invalid}      = invalid
  ≤ᵣ-refl {route l cs p} = comm≤ refl ≈ₚ-refl ≤ᶜˢ-refl

  ≤ᵣ-reflexive : _≈ᵣ_ ⇒ _≤ᵣ_
  ≤ᵣ-reflexive invalidEq               = invalid
  ≤ᵣ-reflexive (routeEq k≡l cs≈ds p≈q) = comm≤ k≡l p≈q (≤ᶜˢ-reflexive cs≈ds)
  
  ≤ᵣ-trans : Transitive _≤ᵣ_
  ≤ᵣ-trans invalid                   invalid                   = invalid
  ≤ᵣ-trans (level<  l<k)             invalid                   = invalid
  ≤ᵣ-trans (level<  l<k)             (level<  k<m)             = level< (<-trans l<k k<m)
  ≤ᵣ-trans (level<  l<k)             (length< k≡m |q|<|r|)     = level< (subst (_ <_) k≡m l<k)
  ≤ᵣ-trans (level<  l<k)             (plex<   k≡m |q|≡|r| q<r) = level< (subst (_ <_) k≡m l<k)
  ≤ᵣ-trans (level<  l<k)             (comm≤   k≡m q≈r ds≤es)   = level< (subst (_ <_) k≡m l<k)
  ≤ᵣ-trans (length< l≡k |p|<|q|)     invalid                   = invalid
  ≤ᵣ-trans (length< l≡k |p|<|q|)     (level<  k<m)             = level< (subst (_< _) (sym l≡k) k<m)
  ≤ᵣ-trans (length< l≡k |p|<|q|)     (length< k≡m |q|<|r|)     = length< (trans l≡k k≡m) (<-trans |p|<|q| |q|<|r|)
  ≤ᵣ-trans (length< l≡k |p|<|q|)     (plex<   k≡m |q|≡|r| q<r) = length< (trans l≡k k≡m) (subst (_ <_) |q|≡|r| |p|<|q|)
  ≤ᵣ-trans (length< l≡k |p|<|q|)     (comm≤   k≡m q≈r ds≤es)   = length< (trans l≡k k≡m) (subst (_ <_) (length-cong q≈r) |p|<|q|)
  ≤ᵣ-trans (plex<   l≡k |p|≡|q| p<q) invalid                   = invalid
  ≤ᵣ-trans (plex<   l≡k |p|≡|q| p<q) (level<  k<m)             = level< (subst (_< _) (sym l≡k) k<m)
  ≤ᵣ-trans (plex<   l≡k |p|≡|q| p<q) (length< k≡m |q|<|r|)     = length< (trans l≡k k≡m) (subst (_< _) (sym |p|≡|q|) |q|<|r|)
  ≤ᵣ-trans (plex<   l≡k |p|≡|q| p<q) (plex<   k≡m |q|≡|r| q<r) = plex< (trans l≡k k≡m) (trans |p|≡|q| |q|≡|r|) (<ₗₑₓ-trans p<q q<r)
  ≤ᵣ-trans (plex<   l≡k |p|≡|q| p<q) (comm≤   k≡m q≈r ds≤es)   = plex< (trans l≡k k≡m) (trans |p|≡|q| (length-cong q≈r)) (proj₁ <ₗₑₓ-resp-≈ q≈r p<q)
  ≤ᵣ-trans (comm≤   l≡k p≈q cs≤ds)   invalid                   = invalid
  ≤ᵣ-trans (comm≤   l≡k p≈q cs≤ds)   (level<  k<m)             = level< (subst (_< _) (sym l≡k) k<m)
  ≤ᵣ-trans (comm≤   l≡k p≈q cs≤ds)   (length< k≡m |q|<|r|)     = length< (trans l≡k k≡m) (subst (_< _) (length-cong (≈ₚ-sym p≈q)) |q|<|r|)
  ≤ᵣ-trans (comm≤   l≡k p≈q cs≤ds)   (plex<   k≡m |q|≡|r| q<r) = plex< (trans l≡k k≡m) (trans (length-cong p≈q) |q|≡|r|) (proj₂ <ₗₑₓ-resp-≈ (≈ₚ-sym p≈q) q<r)
  ≤ᵣ-trans (comm≤   l≡k p≈q cs≤ds)   (comm≤   k≡m q≈r ds≤es)   = comm≤ (trans l≡k k≡m) (≈ₚ-trans p≈q q≈r) (≤ᶜˢ-trans cs≤ds ds≤es)

  ≤ᵣ-antisym : Antisymmetric _≈ᵣ_ _≤ᵣ_
  ≤ᵣ-antisym invalid                 invalid               = invalidEq
  ≤ᵣ-antisym (level<  k<l)           (level<  l<k)         = contradiction k<l (<-asym l<k)
  ≤ᵣ-antisym (level<  k<l)           (length< refl _)      = contradiction k<l (<-irrefl refl)
  ≤ᵣ-antisym (level<  k<l)           (plex<   refl _ _)    = contradiction k<l (<-irrefl refl)
  ≤ᵣ-antisym (level<  k<l)           (comm≤   refl _ _)    = contradiction k<l (<-irrefl refl)
  ≤ᵣ-antisym (length< refl _)        (level<  l<k)         = contradiction l<k (<-irrefl refl)
  ≤ᵣ-antisym (length< _ |p|<|q|)     (length< _ |q|<|p|)   = contradiction |p|<|q| (<-asym |q|<|p|)
  ≤ᵣ-antisym (length< _ |p|<|q|)     (plex<   _ |q|≡|p| _) = contradiction |p|<|q| (<-irrefl (sym |q|≡|p|))
  ≤ᵣ-antisym (length< _ |p|<|q|)     (comm≤   _ q≈p _)     = contradiction |p|<|q| (<-irrefl (sym (length-cong q≈p)))
  ≤ᵣ-antisym (plex<   refl _ _)      (level< l<k)          = contradiction l<k (<-irrefl refl)
  ≤ᵣ-antisym (plex<   _ |p|≡|q| _)   (length< _ |q|<|p|)   = contradiction |q|<|p| (<-irrefl (sym |p|≡|q|))
  ≤ᵣ-antisym (plex<   _ _ p<q)       (plex< _ _ q<p)       = contradiction p<q (<ₗₑₓ-asym q<p)
  ≤ᵣ-antisym (plex<   _ _ p<q)       (comm≤ _ q≈p _)       = contradiction p<q (<ₗₑₓ-irrefl (≈ₚ-sym q≈p))
  ≤ᵣ-antisym (comm≤   refl _ _)      (level< l<k)          = contradiction l<k (<-irrefl refl)
  ≤ᵣ-antisym (comm≤   _ p≈q _)       (length< _ |q|<|p|)   = contradiction |q|<|p| (<-irrefl (sym (length-cong p≈q)))
  ≤ᵣ-antisym (comm≤   _ p≈q _)       (plex< _ _ q<p)       = contradiction q<p (<ₗₑₓ-irrefl (≈ₚ-sym p≈q))
  ≤ᵣ-antisym (comm≤   k≡l p≈q cs≤ds) (comm≤ _ _ ds≤cs)     = routeEq k≡l (≤ᶜˢ-antisym cs≤ds ds≤cs) p≈q

  ≤ᵣ-minimum : Minimum _≤ᵣ_ (route 0 ∅ [])
  ≤ᵣ-minimum invalid        = invalid
  ≤ᵣ-minimum (route l cs p) with <-cmp 0 l
  ... | tri< 0<l _ _ = level< 0<l
  ... | tri> _ _ ()
  ... | tri≈ _ 0≡l _ with <-cmp 0 (length p)
  ...   | tri< 0<|p| _ _ = length< 0≡l 0<|p|
  ...   | tri> _ _ () 
  ...   | tri≈ _ 0≡|p| _ with <ₗₑₓ-cmp [] p
  ...     | tri< []<p _ _ = plex< 0≡l 0≡|p| []<p
  ...     | tri> _ _ p<[] = contradiction (<ₗₑₓ-minimum p) (<ₗₑₓ-asym p<[])
  ...     | tri≈ _ []≈p _ with ≤ᶜˢ-total ∅ cs
  ...       | inj₁ ∅≤cs = comm≤ 0≡l []≈p ∅≤cs
  ...       | inj₂ cs≤∅ = ≤ᵣ-reflexive (routeEq 0≡l (≤ᶜˢ-antisym (≤ᶜˢ-minimum cs) cs≤∅) []≈p)
  
  ≤ᵣ-maximum : Maximum _≤ᵣ_ invalid
  ≤ᵣ-maximum x = invalid

  ≤ᵣ-respˡ-≈ᵣ : ∀ {x y z} → y ≈ᵣ z → x ≤ᵣ y → x ≤ᵣ z
  ≤ᵣ-respˡ-≈ᵣ invalidEq                invalid                   = invalid
  ≤ᵣ-respˡ-≈ᵣ (routeEq refl _     _)   (level<  k<l)             = level<  k<l
  ≤ᵣ-respˡ-≈ᵣ (routeEq refl ds≈es q≈r) (length< k≡l |p|<|q|)     = length< k≡l (subst (_ <_) (length-cong q≈r) |p|<|q|)
  ≤ᵣ-respˡ-≈ᵣ (routeEq refl ds≈es q≈r) (plex<   k≡l |p|≡|q| p<q) = plex<   k≡l (trans |p|≡|q| (length-cong q≈r)) (<ₗₑₓ-respˡ-≈ q≈r p<q)
  ≤ᵣ-respˡ-≈ᵣ (routeEq refl ds≈es q≈r) (comm≤   k≡l p≈q cs≤ds)   = comm≤   k≡l (≈ₚ-trans p≈q q≈r) (≤ᶜˢ-respˡ-≈ᶜˢ ds≈es cs≤ds)

  ≤ᵣ-respʳ-≈ᵣ : ∀ {x y z} → y ≈ᵣ z → y ≤ᵣ x → z ≤ᵣ x
  ≤ᵣ-respʳ-≈ᵣ _                        invalid                   = invalid
  ≤ᵣ-respʳ-≈ᵣ (routeEq refl _     _)   (level<  l<k)             = level<  l<k
  ≤ᵣ-respʳ-≈ᵣ (routeEq refl ds≈es q≈r) (length< l≡k |q|<|p|)     = length< l≡k (subst (_< _) (length-cong q≈r) |q|<|p|)
  ≤ᵣ-respʳ-≈ᵣ (routeEq refl ds≈es q≈r) (plex<   l≡k |q|≡|p| q<p) = plex<   l≡k (trans (sym (length-cong q≈r)) |q|≡|p|) (<ₗₑₓ-respʳ-≈ q≈r q<p)
  ≤ᵣ-respʳ-≈ᵣ (routeEq refl ds≈es q≈r) (comm≤   l≡k q≈p ds≤cs)   = comm≤   l≡k (≈ₚ-trans (≈ₚ-sym q≈r) q≈p) (≤ᶜˢ-respʳ-≈ᶜˢ ds≈es ds≤cs)
  
  ≤ᵣ-resp-≈ᵣ : _≤ᵣ_ Respects₂ _≈ᵣ_
  ≤ᵣ-resp-≈ᵣ = ≤ᵣ-respˡ-≈ᵣ , ≤ᵣ-respʳ-≈ᵣ
